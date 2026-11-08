/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarResidualBlock
public import Bandits.Support.ReferenceGeneratedCalendarNativePreservation

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Generated-calendar endpoint and complete assignment-vector mixtures

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

All readouts below belong to the actual `CalendarSample`, `calendarLaw` and
`calendarObservation`. Auxiliary replacement regenerates the observer from the
raw sample, retaining every physical coordinate and previously inserted vector.
Event measures are unnormalized. These internal probability identities do not
assert the later joint splice law or a regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedNativeInvocationGeometry
open ReferenceActualCollectionHiddenRefreshPath
open ReferencePostInvocationRetainedEndpointRecurrence
open ReferencePostInvocationGeneratedAlignment
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)

namespace Bandits.Support.ReferenceGeneratedCalendarEndpointMixture

variable {p : ConstructorDimensions.Parameters}

local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Outcome" => AssignmentParameterFibreKernel.Outcome p
local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance sumMeasurableSingleton {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] : MeasurableSingletonClass (X ⊕ Y) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
    | inr a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inr_image
local instance optionMeasurableSingleton {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSingletonClass (Option X) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit X))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit X) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit X).injective.eq_iff.symm
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩
local instance outcomeMeasurableSpace : MeasurableSpace Outcome := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace Outcome := ⟨fun _ => trivial⟩

private theorem measurable_sigma_elim {I X : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] [MeasurableSpace X]
    (f : Sigma B → X) (hf : ∀ i, Measurable (fun x : B i => f ⟨i, x⟩)) : Measurable f := by
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hU

private theorem measurable_option_cases {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun x => match o x with | none => f x | some a => g (x, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "withAux" => calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0
local notation "lastFlags" => calendarLastFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "lastEvent" => calendarLastCallEvent rate rewards C_star C_h control0 b0 u0 t0
local notation "nativeRenewal" => calendarNativeRenewal rate rewards C_star C_h control0 b0 u0 t0
local notation "nativeSource" => calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0
local notation "sourceCall" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
local notation "start " z:max => physicalStart rate z rewards C_star C_h
local notation "records " z:max => completeSuffixRecords rate z rewards C_star C_h

/-- The literal incoming logical endpoint; absence is retained. -/
def calendarEndpoint (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) : Outcome :=
  (observe k hk w).2.val.2.2.2.map Prod.fst

local notation "endpoint" => calendarEndpoint rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarEndpoint (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (endpoint k hk) := by
  have hm : Measurable (fun o : TaggedPrefix rate (calendarBoundary t0 k hk) =>
      o.2.val.2.2.2.map Prod.fst) := by
    apply measurable_sigma_elim
    intro s
    have h : Measurable (fun o : PrefixObservation rate s (calendarBoundary t0 k hk) =>
        o.2.2.2.map Prod.fst) := by
      convert measurable_option_cases _ measurable_snd.snd.snd
        (fun _ : PrefixObservation rate s (calendarBoundary t0 k hk) => (none : Outcome)) measurable_const
        (fun v : PrefixObservation rate s (calendarBoundary t0 k hk) ×
          (SlowSet p × List (LogicalCell p rate)) => some v.2.1)
        ((measurable_of_countable (some : SlowSet p → Outcome)).comp measurable_snd.fst) using 1
      funext o
      cases o.2.2.2 <;> rfl
    exact h.comp measurable_subtype_coe
  exact hm.comp (measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk)

/-- The native orientation is the first component of the actual last-call
flags, rather than the original branch bit. -/
theorem calendarNativeRenewal_eq_lastFlags (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    nativeRenewal k hk w = (lastFlags k hk w).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (if callFlag k hk w.1 = true then (pending k hk w.1).1
        else nativeRenewal k (by omega) w.1) =
          (if callFlag k hk w.1 = true then pending k hk w.1 else lastFlags k (by omega) w.1).1
      split <;> simp only [ih]

/-- Literal last-native/local-orientation and current call/renewal/PRE-clear
section. The native PRE-clear bit is kept separate from the current one. -/
def calendarEndpointSection (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : Set (Sample k) :=
  lastEvent bs clear s k hk.le ∩
    {w | callFlag k (by omega) w = true ∧ pending k (by omega) w = (renewed, true)}

local notation "sectionEvent" => calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0

theorem measurableSet_calendarEndpointSection (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : MeasurableSet (sectionEvent renewed bs clear s k hk) :=
  (measurableSet_calendarLastCallEvent rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk.le).inter
    ((measurableSet_eq_fun
      (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
      measurable_const).inter (measurableSet_eq_fun
        (measurable_calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
        measurable_const))

/-- Additional literal restrictions are invariant because the actual source
and its numerical PRE are unchanged by replacing the analytical tape. -/
theorem calendarEndpointSection_withAuxiliary (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) (w : Sample k) (a : Auxiliary) :
    withAux k (w, a) ∈ sectionEvent renewed bs clear s k hk ↔
      w ∈ sectionEvent renewed bs clear s k hk := by
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  rw [calendarLastCallEvent_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk.le hs,
    calendarCallFlag_withAuxiliary, calendarPendingFlags_withAuxiliary]

omit control0 b0 u0 t0 in
private theorem cutoff_record (e n : ℕ) (z : Source)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n) :
    actualRecord rate rewards C_star C_h (cutoffDate rate rewards C_star C_h e n z hz) z =
      some ((records z)[e]'(collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose) := by
  have he := (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose
  change (if start z ≤ start z + e then (records z)[start z + e - start z]? else none) = _
  rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem he]

omit control0 b0 u0 t0 in
private theorem continuing_not_cutoff (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (h : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have hp : (ReferenceActivePhysicalStep.prepare r.input).coordinator = r.output.preparation.coordinator := by
    rw [r.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [hp]
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at h
  cases hc : r.output.preparation.coordinator <;> simp only [hc] at h ⊢
  next r q base outcome => cases outcome <;> simp_all only

omit control0 b0 u0 t0 in
private theorem native_window_collection (e n : ℕ) (z : Source)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (s q : Fin p.T) (hsq : s.val < q.val)
    (zs : InvocationSource rate rewards C_star C_h s) (hzs : zs.val = z)
    (hdate : start z + n = q.val) (hbetween : NoCallBetween rate rewards C_star C_h s q.castSucc z)
    (k : ℕ) (hk : e + k < n) :
    z ∈ collectionDateDomain rate rewards C_star C_h ⟨start z + e + k, by omega⟩ := by
  have hafter := native_before_cutoff rate rewards C_star C_h e n z hz s q hsq zs hzs hdate
  have hepos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  induction k with
  | zero =>
      let v := cutoffDate rate rewards C_star C_h e n z hz
      have hn := hbetween v hafter (by change start z + e < q.val; omega)
      rcases noncall_phase_coverage rate rewards C_star C_h v z (by change start z < start z + e; omega) hn with hl | hc
      · have hr := (continuingSourceCell_spec rate rewards C_star C_h v ⟨z, hl⟩).1
        have heq := Option.some.inj (hr.symm.trans (cutoff_record rate rewards C_star C_h e n z hz))
        have hn := continuing_not_cutoff rate _
          (continuingRecord_frame rate rewards C_star C_h v ⟨z, hl⟩).choose_spec.choose_spec.choose_spec.choose_spec.2.1
        rw [heq, (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose_spec.choose_spec.choose_spec.choose_spec.2.1]
          at hn
        cases hn
      · exact hc
  | succ k ih =>
      let v : Fin p.T := ⟨start z + e + k, by omega⟩
      let v' : Fin p.T := ⟨start z + e + (k + 1), by omega⟩
      have hc : z ∈ collectionDateDomain rate rewards C_star C_h v := ih (by omega)
      have hv := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
      obtain ⟨ledger, saved, hout⟩ := collectionRecord_output rate rewards C_star C_h v ⟨z, hc⟩
      have hn := hbetween v' (by dsimp only [v']; omega) (by change start z + e + (k + 1) < q.val; omega)
      rcases noncall_phase_coverage rate rewards C_star C_h v' z (by dsimp only [v']; omega) hn with hl | hc'
      · obtain ⟨r, owned, base, started, hin, _⟩ := continuingRecord_frame rate rewards C_star C_h v' ⟨z, hl⟩
        have hv' := (continuingSourceCell_spec rate rewards C_star C_h v' ⟨z, hl⟩).1
        have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
          (actualRecord_adjacent rate rewards C_star C_h v v' (by dsimp only [v, v']; omega) z _ _ hv hv')
        rw [hin, hout] at hadj
        cases hadj
      · exact hc'

omit control0 b0 u0 t0 in
private theorem native_trigger_unique (e e' n : ℕ) (z : Source)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (hz' : z ∈ collectionPrefixCell rate rewards C_star C_h e' n)
    (s q : Fin p.T) (hsq : s.val < q.val) (zs : InvocationSource rate rewards C_star C_h s)
    (hzs : zs.val = z) (hdate : start z + n = q.val)
    (hbetween : NoCallBetween rate rewards C_star C_h s q.castSucc z) : e = e' := by
  suffices ∀ i j, z ∈ collectionPrefixCell rate rewards C_star C_h i n →
      z ∈ collectionPrefixCell rate rewards C_star C_h j n → ¬ i < j by
    have h1 := this e e' hz hz'
    have h2 := this e' e hz' hz
    omega
  intro i j hi hj hij
  let v : Fin p.T := ⟨start z + j - 1, by have := hj.1; omega⟩
  let v' := cutoffDate rate rewards C_star C_h j n z hj
  have hc : z ∈ collectionDateDomain rate rewards C_star C_h v := by
    have hh := native_window_collection rate rewards C_star C_h i n z hi s q hsq zs hzs
      hdate hbetween (j - 1 - i) (by have := hj.1; omega)
    convert hh using 1
    congr 1
    apply Fin.ext
    dsimp only [v]
    omega
  have hv := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
  obtain ⟨ledger, saved, hout⟩ := collectionRecord_output rate rewards C_star C_h v ⟨z, hc⟩
  obtain ⟨he, r, owned, base, hin, _⟩ := collectionPrefixCell_live rate rewards C_star C_h j n z hj
  have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
    (actualRecord_adjacent rate rewards C_star C_h v v' (by dsimp only [v, v', cutoffDate]; omega)
      z _ _ hv (cutoff_record rate rewards C_star C_h j n z hj))
  rw [hin, hout] at hadj
  cases hadj

/-- Actual generated retained endpoint atoms after refilling the last native
UPDATE and every later original pair. All finite atoms, including none, occur
in the statement; the none mass is proved zero on this literal section. -/
theorem calendar_retained_refresh_atoms (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent false bs clear s k hk) :
    ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta) ∧
      AssignmentParameterFibreKernel.fibreMass p theta none = 0 ∧
      ∀ (old : OldAuxiliary bs s) (A : Outcome),
        refreshAuxiliaryLaw bs s {a | endpoint k hk.le
          (withAux k (w, (refreshSplit bs s).symm (old, a))) = A} =
            AssignmentParameterFibreKernel.fibreMass p theta A := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  have hc : (sourceCall q (nativeSource k hk.le w).val).isSome = true := hw.2.1
  have hnr : renewalFlag rate rewards C_star C_h (t := (observe k hk.le w).1) q
      (observe k hk.le w).2.val = false := congrArg Prod.fst hw.2.2
  have hclear : preClearFlag rate (t := (observe k hk.le w).1) q
      (observe k hk.le w).2.val = true := congrArg Prod.snd hw.2.2
  obtain ⟨e, n, cutoff, theta, hz, hcall, hdate, hm, ha, _hp, _hnum, _hrank, htrigger, _hpath, _hinj, _hunused⟩ :=
    calendarObservation_retained_endpoint rate rewards C_star C_h control0 b0 u0 t0 k hk w hc hnr hclear
  let z := current k hk.le w
  change z ∈ collectionPrefixCell rate rewards C_star C_h e n at hz
  change sourceCall q z = some (cutoff, theta) at hcall
  change start z + n = q.val at hdate
  have hsq : s.val < q.val := by
    have ho := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
    simpa only [hw.1.1, calendarBoundary, q] using ho
  have hzs : (nativeSource k hk.le w).val = z := rfl
  have hbetween : NoCallBetween rate rewards C_star C_h s q.castSucc z := by
    have hb : calendarBoundary t0 k hk.le = q.castSucc := Fin.ext rfl
    rw [← hb]
    simpa only [hw.1.1, z, calendarCurrentSource] using
      (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).2.2
  have htriggerS : s.val ≤ start z + e - 1 := by
    simpa only [hw.1.1, calendarNativeSource, z, calendarCurrentSource] using htrigger
  have hret (old : OldAuxiliary bs s) (a : RefreshAuxiliary bs s) :
      endpoint k hk.le (withAux k (w, (refreshSplit bs s).symm (old, a))) =
        some (sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl
          (evaluatorArray bs s ((refreshSplit bs s).symm (old, a))) (Fin.last (n - e))) := by
    let w' := withAux k (w, (refreshSplit bs s).symm (old, a))
    have hsource : current k hk.le w' = z :=
      (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w _).2
    have htag : (observe k hk.le w').1 = s :=
      (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w _).1.trans hw.1.1
    have hw' : w' ∈ sectionEvent false bs clear s k hk :=
      (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk
        hsq w _).mpr hw
    have hb' : nativeRenewal k hk.le w' = bs :=
      (calendarNativeRenewal_eq_lastFlags rate rewards C_star C_h control0 b0 u0 t0 k hk.le w').trans
        (congrArg Prod.fst hw'.1.2)
    obtain ⟨e', n', cutoff', theta', hz', _hc', hd', _hm', _ha', _hp', _hn', _hr', _ht', hret', _hi', _hu'⟩ :=
      calendarObservation_retained_endpoint rate rewards C_star C_h control0 b0 u0 t0 k hk w'
        hw'.2.1 (congrArg Prod.fst hw'.2.2) (congrArg Prod.snd hw'.2.2)
    dsimp only [calendarNativeSource] at hz' hd' hret'
    change current k hk.le w' ∈ collectionPrefixCell rate rewards C_star C_h e' n' at hz'
    change start (current k hk.le w') + n' = q.val at hd'
    rw [hsource] at hz' hd'
    have hn : n' = n := by omega
    subst n'
    have he : e' = e := native_trigger_unique rate rewards C_star C_h e' e n z hz' hz
      (observe k hk.le w).1 q
      (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
      (nativeSource k hk.le w) hzs hdate
      (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).2.2
    subst e'
    change endpoint k hk.le w' = some (sampledArrayPath rate rewards C_star C_h e n
      (current k hk.le w') _ (n - e) le_rfl
      (evaluatorArray (nativeRenewal k hk.le w') (observe k hk.le w').1 (original k w').1.2)
      (Fin.last (n - e))) at hret'
    have horig : (original k w').1.2 = (refreshSplit bs s).symm (old, a) :=
      congrArg (fun v => v.1.2) (calendarOriginalLift_withAuxiliary rate rewards C_star C_h b0 u0 t0 k w _)
    simpa only [hsource, htag, hb', horig] using hret'
  let L := collectionWord rate rewards C_star C_h e n z hz
  let P := oldPayload rate rewards C_star C_h e n z hz
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have he := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  have hb := collectionWord_bound rate rewards C_star C_h e n z hz
  let cap := ReferenceActualCollectionNonrenewedEndpointFibreJoin.collectionQueue_sourceCap rate
  let mass := RecordedCorrectedWindow.actualPrefixSamplerMass p Q cap L e n he hz.1 hb
  have htheta : theta = (mass.weight, P.anchor) := Prod.ext hm ha
  have hsampler (v : Vector) : AssignmentParameterFibreKernel.successfulSlowSet p theta v =
      some (CorrectedAssignmentVector.correctedSlowSampler p Q cap L e n he hz.1 hb P.anchor P.anchor_pos v) := by
    rw [htheta]
    exact CheckedAssignmentSample.actualCorrected_successfulSlowSet_eq_sampler p Q cap L e n he hz.1 hb
      P.anchor P.anchor_pos v
  have hnone : AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
    change ContinuousControlSlice.assignmentLaw p.K {v | _ = none} = 0
    simp_rw [hsampler]
    simp only [reduceCtorEq, Set.ofPred_false, measure_empty]
  refine ⟨cutoff, theta, hcall, hnone, ?_⟩
  intro old A
  cases A with
  | none =>
      simp_rw [hret]
      simp only [reduceCtorEq, Set.ofPred_false, measure_empty, hnone]
  | some U =>
      simp_rw [hret, Option.some.injEq]
      rw [refresh_sampledArrayPath_atom rate rewards C_star C_h bs s e n z hz htriggerS old U]
      have hfibre : AssignmentParameterFibreKernel.fibreMass p theta (some U) =
          ENNReal.ofReal (CorrectedAssignmentVector.slowFibreMass p Q cap L e n he hz.1 hb
            P.anchor P.anchor_pos U) := by
        rw [htheta]
        exact CheckedAssignmentSample.actualCorrected_checkedSlow_fibreMass p Q cap L e n he hz.1 hb
          P.anchor P.anchor_pos U
      have hendpoint := ReferenceActualCollectionEnabledPrefixEndpoint.actual_collection_endpoint_atom
        rate rewards C_star C_h e n z hz U
      exact (MeasureTheory.ofReal_measureReal).symm.trans
        ((congrArg ENNReal.ofReal hendpoint).trans hfibre.symm)

omit b0 u0 t0 in
private theorem calendarVectorKernel_of_flags (q : Fin p.T) (o : TaggedPrefix rate q.castSucc)
    (a : Auxiliary) (renewed : Bool) (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : sourceCall q o.2.val.1.1.1.2 = some (cutoff, theta))
    (hclear : preClearFlag rate (t := o.1) q o.2.val = true)
    (hr : renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val = renewed) :
    calendarVectorKernel rate rewards C_star C_h control0 q (o, a) =
      AssignmentParameterFibreKernel.fibreMeasure p theta
        (if renewed then freshEndpoint (p := p) theta (a (q, 1))
          else retainedEndpoint rate (t := o.1) q o.2.val) := by
  rw [calendarVectorKernel_apply,
    nextVectorKernel_of_call rate rewards C_star C_h (t := o.1) (q := q) control0
      (o.2.val, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q a) cutoff theta hc hclear]
  change AssignmentParameterFibreKernel.fibreMeasure p theta
    (if renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val then
      freshEndpoint (p := p) theta (a (q, 1)) else retainedEndpoint rate (t := o.1) q o.2.val) = _
  rw [hr]

/-- Evaluate the actual produced extension kernel on its literal section.
Renewal consumes current label one for initialization, leaving zero for UPDATE. -/
theorem calendarExtensionKernel_onSection (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent renewed bs clear s k hk)
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta)) :
    extension k (by omega) w = AssignmentParameterFibreKernel.fibreMeasure p theta
      (if renewed then freshEndpoint (p := p) theta ((original k w).1.2 (⟨t0.val + 1 + k, hk⟩, 1))
        else endpoint k hk.le w) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  have hclear : preClearFlag rate (t := o.1) q o.2.val = true := congrArg Prod.snd hw.2.2
  have hrenew : renewalFlag rate rewards C_star C_h (t := o.1) q o.2.val = renewed :=
    congrArg Prod.fst hw.2.2
  rw [calendarExtensionKernel_apply]
  exact calendarVectorKernel_of_flags rate rewards C_star C_h control0 q o (original k w).1.2
    renewed cutoff theta hc hclear hrenew

/-- Joint retained endpoint/full K+1-vector fibre identity on an actual
regenerated section. Null atoms cancel without normalization by event mass. -/
theorem calendar_retained_vector_fibre (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent false bs clear s k hk) :
    ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta) ∧
      ∀ (old : OldAuxiliary bs s) (A : Outcome) (C : Set Vector), MeasurableSet C →
        (∫⁻ a, if endpoint k hk.le (withAux k (w, (refreshSplit bs s).symm (old, a))) = A then
          extension k (by omega) (withAux k (w, (refreshSplit bs s).symm (old, a))) C else 0
          ∂refreshAuxiliaryLaw bs s) =
            ContinuousControlSlice.assignmentLaw p.K
              (C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p theta v = A}) := by
  obtain ⟨cutoff, theta, hc, _hnone, hatom⟩ :=
    calendar_retained_refresh_atoms rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw
  have hs : s.val < t0.val + 1 + k := by
    have h := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
    simpa only [hw.1.1, calendarBoundary] using h
  refine ⟨cutoff, theta, hc, ?_⟩
  intro old A C hC
  let wa := fun a : RefreshAuxiliary bs s => withAux k (w, (refreshSplit bs s).symm (old, a))
  have hwa : Measurable wa := (measurable_calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k).comp
    (measurable_const.prodMk ((refreshSplit bs s).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have he := (measurable_calendarEndpoint rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp hwa
  have hS : MeasurableSet {a | endpoint k hk.le (wa a) = A} := measurableSet_eq_fun he measurable_const
  have hkernel (a) : extension k (by omega) (wa a) =
      AssignmentParameterFibreKernel.fibreMeasure p theta (endpoint k hk.le (wa a)) := by
    have hw' : wa a ∈ sectionEvent false bs clear s k hk :=
      (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs w _).mpr hw
    have hz := (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
      ((refreshSplit bs s).symm (old, a))).2
    have hc' : sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le (wa a)) = some (cutoff, theta) := by
      rw [hz]
      exact hc
    exact calendarExtensionKernel_onSection rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk
      (wa a) hw' cutoff theta hc'
  have htest : (fun a => if endpoint k hk.le (wa a) = A then extension k (by omega) (wa a) C else 0) =
      {a | endpoint k hk.le (wa a) = A}.indicator
        (fun _ => AssignmentParameterFibreKernel.fibreMeasure p theta A C) := by
    funext a
    by_cases h : endpoint k hk.le (wa a) = A <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, hkernel, h, ite_true, ite_false]
  change (∫⁻ a, if endpoint k hk.le (wa a) = A then extension k (by omega) (wa a) C else 0
    ∂refreshAuxiliaryLaw bs s) = _
  rw [htest, lintegral_indicator_const hS, hatom old A, mul_comm]
  have hcancel := congrArg (fun mu : Measure Vector => mu C)
    (AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure p theta A)
  simpa only [Measure.smul_apply, Measure.restrict_apply hC, smul_eq_mul,
    FiniteFibreLift.fibre, Set.preimage_singleton] using hcancel

/-- Averaging the actual retained extension kernel yields the whole
assignment cube, rather than only its selected slow-set marginal. -/
theorem calendar_retained_vector_marginal (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent false bs clear s k hk)
    (old : OldAuxiliary bs s) (C : Set Vector) (hC : MeasurableSet C) :
    (∫⁻ a, extension k (by omega) (withAux k (w, (refreshSplit bs s).symm (old, a))) C
      ∂refreshAuxiliaryLaw bs s) = ContinuousControlSlice.assignmentLaw p.K C := by
  obtain ⟨cutoff, theta, _hc, hfibre⟩ :=
    calendar_retained_vector_fibre rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw
  let wa := fun a : RefreshAuxiliary bs s => withAux k (w, (refreshSplit bs s).symm (old, a))
  have hwa : Measurable wa := (measurable_calendarWithAuxiliary rate rewards C_star C_h b0 u0 t0 k).comp
    (measurable_const.prodMk ((refreshSplit bs s).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have he := (measurable_calendarEndpoint rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp hwa
  have hkernel := (ProbabilityTheory.Kernel.measurable_coe (extension k (by omega)) hC).comp hwa
  have hsum := lintegral_finsetSum (μ := refreshAuxiliaryLaw bs s) Finset.univ
    (f := fun A a => if endpoint k hk.le (wa a) = A then extension k (by omega) (wa a) C else 0)
    (fun A _ => Measurable.ite (measurableSet_eq_fun he (measurable_const (a := A))) hkernel measurable_const)
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
  rw [hsum]
  simp_rw [wa, hfibre old _ C hC]
  have h := congrArg (fun mu : Measure Vector => mu C)
    (FiniteFibreLift.sum_restrict_fibre (ContinuousControlSlice.assignmentLaw p.K)
      (AssignmentParameterFibreKernel.successfulSlowSet p theta)
      ((AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
        (measurable_const.prodMk measurable_id)))
  simpa only [Measure.finsetSum_apply, Measure.restrict_apply hC, FiniteFibreLift.fibre,
    Set.preimage_singleton] using h

/-- Null retained fibres have zero probability under the actual refill,
including the absent endpoint. Positivity is an almost-everywhere statement. -/
theorem calendar_retained_refresh_support (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent false bs clear s k hk) :
    ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta) ∧
      ∀ old : OldAuxiliary bs s, ∀ᵐ a ∂refreshAuxiliaryLaw bs s,
        0 < AssignmentParameterFibreKernel.fibreMass p theta
          (endpoint k hk.le (withAux k (w, (refreshSplit bs s).symm (old, a)))) := by
  obtain ⟨cutoff, theta, hc, _hnone, hatom⟩ :=
    calendar_retained_refresh_atoms rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw
  refine ⟨cutoff, theta, hc, ?_⟩
  intro old
  have hall : ∀ᵐ a ∂refreshAuxiliaryLaw bs s, ∀ A : Outcome,
      AssignmentParameterFibreKernel.fibreMass p theta A = 0 →
        endpoint k hk.le (withAux k (w, (refreshSplit bs s).symm (old, a))) ≠ A := by
    apply ae_all_iff.mpr
    intro A
    by_cases hA : AssignmentParameterFibreKernel.fibreMass p theta A = 0
    · have hz := (hatom old A).trans hA
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with a ha
      exact fun _ => ha
    · exact Filter.Eventually.of_forall fun _ h => (hA h).elim
  filter_upwards [hall] with a ha
  exact bot_lt_iff_ne_bot.mpr (fun hz => ha _ hz rfl)

open ReferenceFirstNextLiftFutureAuxiliaryPairLaw

local notation "erasePair" => calendarErasePair rate rewards C_star C_h b0 u0 t0
local notation "fillPair" => calendarFillPair rate rewards C_star C_h b0 u0 t0

/-- Pair refill in the raw calendar is literal original-array replacement. -/
theorem calendarFillPair_eq_withAuxiliary (q : Fin p.T) (k : ℕ) (w : Sample k) (x : Scalar × Scalar) :
    fillPair q k (w, x) = withAux k (w, fillAuxiliaryPair q (original k w).1.2 x) := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext (ih w.1) rfl

/-- At this PRE boundary the current pair has not been consumed, so refilling
it preserves the complete generated observer pointwise. -/
theorem calendarObservation_fillPair (q : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k ≤ p.T) (hq : t0.val + 1 + k ≤ q.val) (w : Sample k) (x : Scalar × Scalar) :
    observe k hk (fillPair q k (w, x)) = observe k hk w := by
  rw [calendarFillPair_eq_withAuxiliary]
  apply calendarObservation_withAuxiliary_prefix
  intro j hj
  apply fillAuxiliaryPair_apply_other
  · intro he
    have hd := congrArg (fun v => v.1.val) he
    change j.1.val = q.val at hd
    omega
  · intro he
    have hd := congrArg (fun v => v.1.val) he
    change j.1.val = q.val at hd
    omega

/-- The initializer actually chosen by the calendar kernel at the current
call. Its parameter below is always identified with that actual call. -/
def calendarChosenEndpoint (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (theta : AssignmentParameterFibreKernel.Theta p) (w : Sample k) : Outcome :=
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o := observe k hk.le w
  installationEndpoint rate rewards C_star C_h (t := o.1) q
    ((o.2.val, auxiliaryPair q (original k w).1.2), theta)

local notation "chosen" => calendarChosenEndpoint rate rewards C_star C_h control0 b0 u0 t0

theorem calendarChosenEndpoint_onSection (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (theta : AssignmentParameterFibreKernel.Theta p) (w : Sample k)
    (hw : w ∈ sectionEvent renewed bs clear s k hk) :
    chosen k hk theta w = if renewed then freshEndpoint theta
      ((original k w).1.2 (⟨t0.val + 1 + k, hk⟩, 1)) else endpoint k hk.le w := by
  have hr : renewalFlag rate rewards C_star C_h (t := (observe k hk.le w).1)
      ⟨t0.val + 1 + k, hk⟩ (observe k hk.le w).2.val = renewed := congrArg Prod.fst hw.2.2
  dsimp only [calendarChosenEndpoint, installationEndpoint, endpointChoice]
  rw [hr]
  rfl

private theorem renewed_refill_kernel (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent true bs clear s k hk)
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta))
    (x : Scalar × Scalar) :
    chosen k hk theta (fillPair ⟨t0.val + 1 + k, hk⟩ k (w, x)) = freshEndpoint theta x.2 ∧
      extension k (by omega) (fillPair ⟨t0.val + 1 + k, hk⟩ k (w, x)) =
        AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x.2) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let w' := fillPair q k (w, x)
  have hs : s.val < t0.val + 1 + k := by
    have h := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
    simpa only [hw.1.1, calendarBoundary] using h
  have hw' : w' ∈ sectionEvent true bs clear s k hk := by
    dsimp only [w']
    rw [calendarFillPair_eq_withAuxiliary]
    exact (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk hs w _).mpr hw
  have ho : observe k hk.le w' = observe k hk.le w :=
    calendarObservation_fillPair rate rewards C_star C_h control0 b0 u0 t0 q k hk.le le_rfl w x
  have hc' : sourceCall q (current k hk.le w') = some (cutoff, theta) := by
    change sourceCall q (observe k hk.le w').2.val.1.1.1.2 = _
    rw [ho]
    exact hc
  have hx : (original k w').1.2 (q, 1) = x.2 := by
    dsimp only [w']
    rw [calendarFillPair_eq_withAuxiliary, calendarOriginalLift_withAuxiliary]
    exact Function.update_self _ _ _
  have hchosen := calendarChosenEndpoint_onSection rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk theta w' hw'
  have hkernel := calendarExtensionKernel_onSection rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk w' hw' cutoff theta hc'
  change chosen k hk theta w' = freshEndpoint theta x.2 ∧
    extension k (by omega) w' = AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x.2)
  change (original k w').1.2 (⟨t0.val + 1 + k, hk⟩, 1) = x.2 at hx
  simpa only [ite_true, hx] using And.intro hchosen hkernel

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem fresh_pair_fibre (theta : AssignmentParameterFibreKernel.Theta p)
    (A : Outcome) (C : Set Vector) (hC : MeasurableSet C) :
    (∫⁻ x : Scalar × Scalar, if freshEndpoint (p := p) theta x.2 = A then
      AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint (p := p) theta x.2) C else 0
      ∂auxiliaryPairLaw) = ContinuousControlSlice.assignmentLaw p.K
        (C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p theta v = A}) := by
  have he : Measurable (fun x : Scalar => freshEndpoint (p := p) theta x) := by
    change Measurable ((fun v : AssignmentParameterFibreKernel.Theta p × Scalar =>
      freshEndpoint (p := p) v.1 v.2) ∘ fun x : Scalar => (theta, x))
    exact (measurable_freshEndpoint (p := p)).comp
      ((measurable_const (a := theta)).prodMk measurable_id)
  have hS : MeasurableSet {x : Scalar × Scalar | freshEndpoint theta x.2 = A} :=
    measurableSet_eq_fun (he.comp measurable_snd) measurable_const
  have htest : (fun x : Scalar × Scalar => if freshEndpoint theta x.2 = A then
      AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x.2) C else 0) =
      {x : Scalar × Scalar | freshEndpoint theta x.2 = A}.indicator
        (fun _ => AssignmentParameterFibreKernel.fibreMeasure p theta A C) := by
    funext x
    by_cases h : freshEndpoint theta x.2 = A <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true, ite_false]
  rw [htest, lintegral_indicator_const hS]
  have hmass : auxiliaryPairLaw {x : Scalar × Scalar | freshEndpoint theta x.2 = A} =
      AssignmentParameterFibreKernel.fibreMass p theta A := by
    have hp := measurePreserving_snd (μ := ContinuousControlSlice.scalarLaw) (ν := ContinuousControlSlice.scalarLaw)
    exact (hp.measure_preimage (measurableSet_eq_fun he measurable_const).nullMeasurableSet).trans
      (ReferenceNextInsertedSourceMarginal.freshEndpoint_fibre theta A)
  rw [hmass, mul_comm]
  have hcanc := congrArg (fun mu : Measure Vector => mu C)
    (AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure p theta A)
  simpa only [Measure.smul_apply, Measure.restrict_apply hC, smul_eq_mul,
    FiniteFibreLift.fibre, Set.preimage_singleton] using hcanc

/-- Actual renewed-call joint endpoint/full-vector fibre law. The original
current pair is refilled in the produced raw sample and its observer regenerated. -/
theorem calendar_renewed_vector_fibre (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent true bs clear s k hk) :
    ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta) ∧
      (∀ x : Scalar × Scalar, 0 < AssignmentParameterFibreKernel.fibreMass p theta
        (chosen k hk theta (fillPair ⟨t0.val + 1 + k, hk⟩ k (w, x)))) ∧
      ∀ (A : Outcome) (C : Set Vector), MeasurableSet C →
        (∫⁻ x : Scalar × Scalar,
          if chosen k hk theta (fillPair ⟨t0.val + 1 + k, hk⟩ k (w, x)) = A then
            extension k (by omega) (fillPair ⟨t0.val + 1 + k, hk⟩ k (w, x)) C else 0 ∂auxiliaryPairLaw) =
          ContinuousControlSlice.assignmentLaw p.K
            (C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p theta v = A}) := by
  have hcall : (sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)).isSome = true := hw.2.1
  obtain ⟨⟨cutoff, theta⟩, hc⟩ := Option.isSome_iff_exists.mp hcall
  have hchosen := fun x => (renewed_refill_kernel rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw cutoff theta hc x).1
  have hkernel := fun x => (renewed_refill_kernel rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw cutoff theta hc x).2
  refine ⟨cutoff, theta, hc, ?_, ?_⟩
  · intro x
    rw [hchosen]
    exact ReferenceNextInsertedSourceMarginal.freshEndpoint_mass_pos theta x.2
  intro A C hC
  calc
    _ = ∫⁻ x : Scalar × Scalar, if freshEndpoint (p := p) theta x.2 = A then
        AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint (p := p) theta x.2) C else 0
        ∂auxiliaryPairLaw := by
      apply lintegral_congr
      intro x
      rw [hchosen x, hkernel x]
    _ = _ := fresh_pair_fibre theta A C hC

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem fresh_pair_marginal (theta : AssignmentParameterFibreKernel.Theta p) (C : Set Vector) :
    (∫⁻ x : Scalar × Scalar, AssignmentParameterFibreKernel.fibreMeasure p theta
      (freshEndpoint (p := p) theta x.2) C ∂auxiliaryPairLaw) = ContinuousControlSlice.assignmentLaw p.K C := by
  have he : Measurable (fun x : Scalar => freshEndpoint (p := p) theta x) := by
    change Measurable ((fun v : AssignmentParameterFibreKernel.Theta p × Scalar =>
      freshEndpoint (p := p) v.1 v.2) ∘ fun x : Scalar => (theta, x))
    exact (measurable_freshEndpoint (p := p)).comp
      ((measurable_const (a := theta)).prodMk measurable_id)
  have hf : Measurable (fun x : Scalar => AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x) C) :=
    (measurable_of_countable (fun A : Outcome => AssignmentParameterFibreKernel.fibreMeasure p theta A C)).comp he
  change (∫⁻ x : Scalar × Scalar, AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x.2) C
    ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) = _
  rw [← lintegral_map hf measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  exact ReferenceNextInsertedSourceMarginal.freshEndpoint_vector_marginal theta C

/-- Actual renewed extension averaged over its fresh current date pair. -/
theorem calendar_renewed_vector_marginal (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent true bs clear s k hk) (C : Set Vector) :
    (∫⁻ x : Scalar × Scalar, extension k (by omega)
      (fillPair ⟨t0.val + 1 + k, hk⟩ k (w, x)) C ∂auxiliaryPairLaw) =
        ContinuousControlSlice.assignmentLaw p.K C := by
  have hcall : (sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)).isSome = true := hw.2.1
  obtain ⟨⟨cutoff, theta⟩, hc⟩ := Option.isSome_iff_exists.mp hcall
  calc
    _ = ∫⁻ x : Scalar × Scalar, AssignmentParameterFibreKernel.fibreMeasure p theta
        (freshEndpoint (p := p) theta x.2) C ∂auxiliaryPairLaw := by
      apply lintegral_congr
      intro x
      rw [(renewed_refill_kernel rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw cutoff theta hc x).2]
    _ = _ := fresh_pair_marginal theta C

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem restrict_factorization
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (mu : Measure B) (nu : Measure X) [SFinite mu] [SFinite nu]
    (e : B → B) (he : Measurable e) (x : B → X) (hx : Measurable x)
    (hbase : mu.map (fun w => (e w, x w)) = (mu.map e).prod nu)
    (E : Set B) (hE : MeasurableSet E) (hinv : e ⁻¹' E = E) :
    (mu.restrict E).map (fun w => (e w, x w)) = ((mu.restrict E).map e).prod nu := by
  have hpre : (fun w => (e w, x w)) ⁻¹' (E ×ˢ Set.univ) = E := by
    ext w
    simpa only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] using Set.ext_iff.mp hinv w
  calc
    _ = (mu.map (fun w => (e w, x w))).restrict (E ×ˢ Set.univ) := by
      rw [Measure.restrict_map (he.prodMk hx) (hE.prod MeasurableSet.univ), hpre]
    _ = ((mu.map e).restrict E).prod nu := by
      rw [hbase, Measure.restrict_prod_eq_prod_univ]
    _ = _ := by rw [Measure.restrict_map he hE, hinv]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem restore_from_split
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (mu : Measure B) (nu : Measure X) (e : B → B) (he : Measurable e)
    (x : B → X) (hx : Measurable x) (r : B × X → B) (hr : Measurable r)
    (hsplit : mu.map (fun w => (e w, x w)) = (mu.map e).prod nu)
    (hroundtrip : ∀ w, r (e w, x w) = w) : mu = ((mu.map e).prod nu).map r := by
  have h := congrArg (fun m : Measure (B × X) => m.map r) hsplit
  rw [Measure.map_map hr (he.prodMk hx)] at h
  have hid : r ∘ (fun w => (e w, x w)) = id := funext hroundtrip
  rwa [hid, Measure.map_id] at h

local notation "eraseBlock" => calendarEraseBlock rate rewards C_star C_h b0 u0 t0
local notation "fillBlock" => calendarFillBlock rate rewards C_star C_h b0 u0 t0

/-- Restrict the accepted residual split by the literal current call,
nonrenewal/renewal and numerical PRE-clear tests, all proved invariant above. -/
theorem calendarLaw_section_eq_restoreBlock (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    (law k hk.le).restrict (sectionEvent renewed bs clear s k hk) =
      ((((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map (eraseBlock bs s k)).prod
        (refreshAuxiliaryLaw bs s)).map (fillBlock bs s k) := by
  let E := sectionEvent renewed bs clear s k hk
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk
  have he := measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k
  have hx := (refreshSplit bs s).measurable.snd.comp
    (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd
  have hinv : eraseBlock bs s k ⁻¹' E = E := Set.ext fun w =>
    calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs w _
  have hrestrict : ((law k hk.le).restrict (lastEvent bs clear s k hk.le)).restrict E =
      (law k hk.le).restrict E := by
    rw [Measure.restrict_restrict hE, Set.inter_eq_left.mpr (fun _ h => h.1)]
  have hsplit := restrict_factorization ((law k hk.le).restrict (lastEvent bs clear s k hk.le))
    (refreshAuxiliaryLaw bs s) (eraseBlock bs s k) he
    (fun w => (refreshSplit bs s (original k w).1.2).2) hx
    (calendarLaw_lastCall_eraseBlock rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk.le hs) E hE hinv
  rw [hrestrict] at hsplit
  exact restore_from_split _ _ _ he _ hx (fillBlock bs s k)
    (measurable_calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k) hsplit
    (calendarFillBlock_erase rate rewards C_star C_h b0 u0 t0 bs s k)

/-- Pair erasure also acts literally on the original auxiliary array. -/
theorem calendarErasePair_eq_withAuxiliary (q : Fin p.T) (k : ℕ) (w : Sample k) :
    erasePair q k w = withAux k (w, eraseAuxiliaryPair q (original k w).1.2) := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext (ih w.1) rfl

/-- The produced current-pair split applied to the same literal call section.
This uses the actual calendar law, including every previous insertion. -/
theorem calendarLaw_section_eq_restorePair (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (law k hk.le).restrict (sectionEvent renewed bs clear s k hk) =
      ((((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map (erasePair q k)).prod
        auxiliaryPairLaw).map (fillPair q k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let E := sectionEvent renewed bs clear s k hk
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk
  have he := measurable_calendarErasePair rate rewards C_star C_h b0 u0 t0 q k
  have hx := (measurable_auxiliaryPair q).comp
    (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd
  have hinv : erasePair q k ⁻¹' E = E := by
    ext w
    rw [Set.mem_preimage, calendarErasePair_eq_withAuxiliary]
    exact calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs w _
  have hsplit := restrict_factorization (law k hk.le) auxiliaryPairLaw (erasePair q k) he
    (fun w => auxiliaryPair q (original k w).1.2) hx
    (calendarLaw_erasePair rate rewards C_star C_h control0 b0 u0 t0 q k hk.le le_rfl) E hE hinv
  exact restore_from_split _ _ _ he _ hx (fillPair q k)
    (measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k) hsplit
    (calendarFillPair_erasePair rate rewards C_star C_h b0 u0 t0 q k)

private theorem withAuxiliary_twice (k : ℕ) (w : Sample k) (a a' : Auxiliary) :
    withAux k (withAux k (w, a), a') = withAux k (w, a') := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext (ih w.1) rfl

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem eraseBlockAuxiliary_fill (bs : Bool) (s : Fin p.T) (a : Auxiliary) (x : RefreshAuxiliary bs s) :
    eraseBlockAuxiliary bs s (fillBlockAuxiliary bs s (a, x)) = eraseBlockAuxiliary bs s a := by
  dsimp only [eraseBlockAuxiliary, fillBlockAuxiliary]
  rw [(refreshSplit bs s).apply_symm_apply]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem eraseBlockAuxiliary_twice (bs : Bool) (s : Fin p.T) (a : Auxiliary) :
    eraseBlockAuxiliary bs s (eraseBlockAuxiliary bs s a) = eraseBlockAuxiliary bs s a := by
  dsimp only [eraseBlockAuxiliary]
  rw [(refreshSplit bs s).apply_symm_apply]

private theorem eraseBlock_fill (bs : Bool) (s : Fin p.T) (k : ℕ) (wx : Sample k × RefreshAuxiliary bs s) :
    eraseBlock bs s k (fillBlock bs s k wx) = eraseBlock bs s k wx.1 := by
  dsimp only [calendarEraseBlock, calendarFillBlock]
  rw [calendarOriginalLift_withAuxiliary, withAuxiliary_twice, eraseBlockAuxiliary_fill]

private theorem eraseBlock_twice (bs : Bool) (s : Fin p.T) (k : ℕ) (w : Sample k) :
    eraseBlock bs s k (eraseBlock bs s k w) = eraseBlock bs s k w := by
  dsimp only [calendarEraseBlock]
  rw [calendarOriginalLift_withAuxiliary, withAuxiliary_twice, eraseBlockAuxiliary_twice]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem eraseAuxiliaryPair_fill (q : Fin p.T) (a : Auxiliary) (x : Scalar × Scalar) :
    eraseAuxiliaryPair q (fillAuxiliaryPair q a x) = eraseAuxiliaryPair q a := by
  funext j
  by_cases h0 : j = (q, 0)
  · subst j; simp [eraseAuxiliaryPair, fillAuxiliaryPair]
  by_cases h1 : j = (q, 1)
  · subst j; simp [eraseAuxiliaryPair, fillAuxiliaryPair]
  rw [eraseAuxiliaryPair_apply_other q _ j h0 h1, eraseAuxiliaryPair_apply_other q _ j h0 h1,
    fillAuxiliaryPair_apply_other q a x j h0 h1]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem eraseAuxiliaryPair_twice (q : Fin p.T) (a : Auxiliary) :
    eraseAuxiliaryPair q (eraseAuxiliaryPair q a) = eraseAuxiliaryPair q a := by
  exact eraseAuxiliaryPair_fill q a
    (ReferenceFirstLiveActualRefreshTestLaw.scalarZero, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)

private theorem erasePair_fill (q : Fin p.T) (k : ℕ) (wx : Sample k × (Scalar × Scalar)) :
    erasePair q k (fillPair q k wx) = erasePair q k wx.1 := by
  rw [calendarFillPair_eq_withAuxiliary, calendarErasePair_eq_withAuxiliary,
    calendarOriginalLift_withAuxiliary, withAuxiliary_twice, eraseAuxiliaryPair_fill,
    calendarErasePair_eq_withAuxiliary]

private theorem erasePair_twice (q : Fin p.T) (k : ℕ) (w : Sample k) :
    erasePair q k (erasePair q k w) = erasePair q k w := by
  rw [calendarErasePair_eq_withAuxiliary, calendarErasePair_eq_withAuxiliary,
    calendarOriginalLift_withAuxiliary, withAuxiliary_twice, eraseAuxiliaryPair_twice]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem refill_kernel_product
    {B X V : Type*} [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (nu : Measure X) [IsProbabilityMeasure nu]
    (lambda : Measure V) [SFinite lambda] (kernel : ProbabilityTheory.Kernel B V)
    [ProbabilityTheory.IsMarkovKernel kernel]
    (e : B → B) (he : Measurable e) (r : B × X → B) (hr : Measurable r)
    (hrestore : mu = ((mu.map e).prod nu).map r)
    (hefill : ∀ wx, e (r wx) = e wx.1) (hid : ∀ w, e (e w) = e w)
    (hmarginal : ∀ C, MeasurableSet C → ∀ᵐ w ∂mu.map e,
      (∫⁻ x, kernel (r (w, x)) C ∂nu) = lambda C) :
    (mu.compProd kernel).map (Prod.map e id) = (mu.map e).prod lambda := by
  apply Measure.ext_prod
  intro S C hS hC
  let F : B → ℝ≥0∞ := fun w => if e w ∈ S then kernel w C else 0
  have hF : Measurable F := (ProbabilityTheory.Kernel.measurable_coe kernel hC).ite
    (hS.preimage he) measurable_const
  have hleft : (mu.compProd kernel).map (Prod.map e id) (S ×ˢ C) = ∫⁻ w, F w ∂mu := by
    rw [Measure.map_apply (he.prodMap measurable_id) (hS.prod hC),
      Measure.compProd_apply ((hS.prod hC).preimage (he.prodMap measurable_id))]
    apply lintegral_congr
    intro w
    change kernel w {v | e w ∈ S ∧ v ∈ C} = F w
    by_cases hw : e w ∈ S
    · simp only [hw, true_and, F, ite_true]
      exact congrArg (fun D : Set V => kernel w D) (Set.ext fun _ => Iff.rfl)
    · simp only [hw, false_and, Set.ofPred_false, F, ite_false, measure_empty]
  rw [hleft, Measure.prod_prod]
  calc
    _ = ∫⁻ w, F w ∂((mu.map e).prod nu).map r :=
      congrArg (fun m : Measure B => ∫⁻ w, F w ∂m) hrestore
    _ = ∫⁻ wx, F (r wx) ∂(mu.map e).prod nu := lintegral_map hF hr
    _ = ∫⁻ w, ∫⁻ x, F (r (w, x)) ∂nu ∂mu.map e :=
      lintegral_prod _ (hF.comp hr).aemeasurable
    _ = ∫⁻ w, (e ⁻¹' S).indicator (fun _ => lambda C) w ∂mu.map e := by
      apply lintegral_congr_ae
      filter_upwards [hmarginal C hC] with w hw
      simp only [F, hefill]
      by_cases hs : e w ∈ S
      · simpa only [hs, ite_true, Set.indicator, Set.mem_preimage] using hw
      · simp only [hs, ite_false, lintegral_zero, Set.indicator, Set.mem_preimage]
    _ = lambda C * (mu.map e) (e ⁻¹' S) := lintegral_indicator_const (hS.preimage he) (lambda C)
    _ = (mu.map e) S * lambda C := by
      have hm : (mu.map e).map e = mu.map e := by
        rw [Measure.map_map he he]
        exact congrArg (fun g : B → B => mu.map g) (funext hid)
      have hmass : (mu.map e) (e ⁻¹' S) = (mu.map e) S := by
        rw [← Measure.map_apply he hS, hm]
      rw [hmass, mul_comm]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem compProd_restrict_fst {B V : Type*} [MeasurableSpace B] [MeasurableSpace V]
    (mu : Measure B) [IsFiniteMeasure mu] (kernel : ProbabilityTheory.Kernel B V)
    [ProbabilityTheory.IsMarkovKernel kernel] (E : Set B) (hE : MeasurableSet E) :
    (mu.compProd kernel).restrict (Prod.fst ⁻¹' E) = (mu.restrict E).compProd kernel := by
  ext S hS
  rw [Measure.restrict_apply hS, Measure.compProd_apply (hS.inter (hE.preimage measurable_fst)),
    Measure.compProd_apply hS, ← lintegral_indicator hE]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ E <;> simp [Set.preimage, hw]

/-- Under the produced retained-call law, the complete new assignment vector
is uniform jointly with the erased raw sample. The observer can be regenerated
from that sample; the un-erased analytical history is not factored. -/
theorem calendarLaw_retained_vector_product (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    ((law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent false bs clear s k hk)).map (Prod.map (eraseBlock bs s k) id) =
      (((law k hk.le).restrict (sectionEvent false bs clear s k hk)).map (eraseBlock bs s k)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  let E := sectionEvent false bs clear s k hk
  let mu := (law k hk.le).restrict E
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk
  have he := measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k
  have hsupport : ∀ᵐ w ∂mu.map (eraseBlock bs s k), w ∈ E := by
    apply (ae_map_iff he.aemeasurable hE).mpr
    filter_upwards [ae_restrict_mem hE] with w hw
    exact (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs w _).mpr hw
  change ((law k hk.le).compProd (extension k (by omega)) |>.restrict (Prod.fst ⁻¹' E)).map _ = _
  rw [compProd_restrict_fst _ _ E hE]
  apply refill_kernel_product mu (refreshAuxiliaryLaw bs s) (ContinuousControlSlice.assignmentLaw p.K)
    (extension k (by omega)) (eraseBlock bs s k) he (fillBlock bs s k)
    (measurable_calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k)
    (calendarLaw_section_eq_restoreBlock rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs)
    (eraseBlock_fill rate rewards C_star C_h b0 u0 t0 bs s k)
    (eraseBlock_twice rate rewards C_star C_h b0 u0 t0 bs s k)
  intro C hC
  filter_upwards [hsupport] with w hw
  exact calendar_retained_vector_marginal rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw
    (refreshSplit bs s (original k w).1.2).1 C hC

/-- Under the produced renewed-call law, the fresh-label mixture gives the
entire assignment cube jointly with the raw sample whose current pair is erased. -/
theorem calendarLaw_renewed_vector_product (bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    ((law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent true bs clear s k hk)).map (Prod.map (erasePair q k) id) =
      (((law k hk.le).restrict (sectionEvent true bs clear s k hk)).map (erasePair q k)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let E := sectionEvent true bs clear s k hk
  let mu := (law k hk.le).restrict E
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk
  have he := measurable_calendarErasePair rate rewards C_star C_h b0 u0 t0 q k
  have hsupport : ∀ᵐ w ∂mu.map (erasePair q k), w ∈ E := by
    apply (ae_map_iff he.aemeasurable hE).mpr
    filter_upwards [ae_restrict_mem hE] with w hw
    rw [calendarErasePair_eq_withAuxiliary]
    exact (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk hs w _).mpr hw
  change ((law k hk.le).compProd (extension k (by omega)) |>.restrict (Prod.fst ⁻¹' E)).map _ = _
  rw [compProd_restrict_fst _ _ E hE]
  apply refill_kernel_product mu auxiliaryPairLaw (ContinuousControlSlice.assignmentLaw p.K)
    (extension k (by omega)) (erasePair q k) he (fillPair q k)
    (measurable_calendarFillPair rate rewards C_star C_h b0 u0 t0 q k)
    (calendarLaw_section_eq_restorePair rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk hs)
    (erasePair_fill rate rewards C_star C_h b0 u0 t0 q k)
    (erasePair_twice rate rewards C_star C_h b0 u0 t0 q k)
  intro C _hC
  filter_upwards [hsupport] with w hw
  exact calendar_renewed_vector_marginal rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw C

/-- The appropriate literal raw erasure for a retained or renewed call. -/
def calendarMixtureErase (renewed bs : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) : Sample k → Sample k :=
  if renewed then erasePair ⟨t0.val + 1 + k, hk⟩ k else eraseBlock bs s k

local notation "mixtureErase" => calendarMixtureErase rate rewards C_star C_h b0 u0 t0

/-- Arbitrary Borel tests of the erased raw sample and the complete new
vector, on either actual call section, with its original unnormalized mass. -/
theorem calendarLaw_endpoint_vector_test (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k)
    (f : Sample k × Vector → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ wv, f (mixtureErase renewed bs s k hk wv.1, wv.2)
      ∂(law (k + 1) (by omega)).restrict (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)) =
      ∫⁻ w, ∫⁻ v, f (w, v) ∂ContinuousControlSlice.assignmentLaw p.K
        ∂((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map (mixtureErase renewed bs s k hk) := by
  have he : Measurable (mixtureErase renewed bs s k hk) := by
    cases renewed
    · exact measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k
    · exact measurable_calendarErasePair rate rewards C_star C_h b0 u0 t0 _ k
  have hprod : ((law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)).map (Prod.map (mixtureErase renewed bs s k hk) id) =
      (((law k hk.le).restrict (sectionEvent renewed bs clear s k hk)).map (mixtureErase renewed bs s k hk)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
    cases renewed
    · exact calendarLaw_retained_vector_product rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs
    · exact calendarLaw_renewed_vector_product rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk hs
  calc
    _ = ∫⁻ wv, f wv ∂((law (k + 1) (by omega)).restrict
        (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk)).map
          (Prod.map (mixtureErase renewed bs s k hk) id) :=
      (lintegral_map hf (he.prodMap measurable_id)).symm
    _ = _ := by rw [hprod]; exact lintegral_prod _ hf.aemeasurable

omit b0 u0 t0 in
include control0 in
private theorem prefixNumerical_insert (q : Fin p.T) (n : Fin (p.T + 1))
    (hn : n.val ≤ q.val) (z : Source) (v : Vector) :
    prefixNumerical rate rewards C_star C_h n (ReferenceFirstCollectionRenewalVectorInsertion.insert q z v) =
      prefixNumerical rate rewards C_star C_h n z := by
  calc
    _ = prefixNumerical rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val
          (ReferenceFirstCollectionRenewalVectorInsertion.insert q z v)) :=
      prefixNumerical_sourcePrefix rate rewards C_star C_h control0 n q.val hn _
    _ = prefixNumerical rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val z) :=
      congrArg (prefixNumerical rate rewards C_star C_h n)
        (ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl z
          (ReferenceFirstCollectionRenewalVectorInsertion.ctrl q z v))
    _ = _ := (prefixNumerical_sourcePrefix rate rewards C_star C_h control0 n q.val hn z).symm

/-- The remembered native PRE-clear bit is the numerical PRE on the SAME
current physical source at its last native date. Later insertions preserve it. -/
theorem calendarLastFlags_nativePreClear (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    (lastFlags k hk w).2 =
      (prefixNumerical rate rewards C_star C_h (observe k hk w).1.castSucc (current k hk w)).any
        (fun S => !S.overflow) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let q : Fin p.T := ⟨t0.val + 1 + k, by omega⟩
      let o : TaggedPrefix rate q.castSucc := observe k (by omega) w.1
      let a := (original k w.1).1.2
      have hstep : observe (k + 1) hk w = calendarStep rate rewards C_star C_h control0 q (o, (a, w.2)) := rfl
      by_cases hc : callFlag k hk w.1 = true
      · have hE : (o.2, (a, w.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
        rw [calendarLastFlags, ite_eq_left hc]
        change (pending k hk w.1).2 =
          (prefixNumerical rate rewards C_star C_h (observe (k + 1) hk w).1.castSucc
            (observe (k + 1) hk w).2.val.1.1.1.2).any (fun S => !S.overflow)
        rw [hstep, calendarStep, dite_eq_left hE]
        change (pending k hk w.1).2 =
          (prefixNumerical rate rewards C_star C_h q.castSucc
            (ReferenceFirstCollectionRenewalVectorInsertion.insert q (current k (by omega) w.1) w.2)).any
              (fun S => !S.overflow)
        rw [prefixNumerical_insert rate rewards C_star C_h control0 q q.castSucc (by rfl)]
        have hn : o.2.val.2.2.1 = prefixNumerical rate rewards C_star C_h q.castSucc
            (current k (by omega) w.1) :=
          calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1
        exact congrArg (fun S : Option (RecordedQueueRun.RunState p.K) => S.any (fun R => !R.overflow)) hn
      · have hE : ¬ (o.2, (a, w.2)) ∈ calendarCallEvent rate rewards C_star C_h o.1 q := hc
        rw [calendarLastFlags, ite_eq_right hc]
        change (lastFlags k (by omega) w.1).2 =
          (prefixNumerical rate rewards C_star C_h (observe (k + 1) hk w).1.castSucc
            (observe (k + 1) hk w).2.val.1.1.1.2).any (fun S => !S.overflow)
        rw [hstep, calendarStep, dite_eq_right hE]
        exact ih (by omega) w.1

omit rewards C_star C_h control0 b0 u0 t0 in
private theorem prefix_clear_mono (W : List (RecordedQueueRun.RoundInput p.K))
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ W.length)
    (hclear : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) (W.take j)).overflow = false) :
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) (W.take i)).overflow = false := by
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  cases hi : (RecordedQueueRun.run Q (W.take i)).overflow with
  | false => rfl
  | true =>
      have hfirst := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W i (hij.trans hj)).mp hi
      have hlate := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le Q W j hj).mpr
        (hfirst.trans hij)
      rw [hclear] at hlate
      cases hlate

/-- Current PRE-clear entails native last-call PRE-clear, derived from the
preserved complete numerical word. This also holds at the terminal boundary. -/
theorem calendarLastFlags_clear_of_preClear (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k)
    (hclear : (observe k hk w).2.val.2.2.1.any (fun S => !S.overflow) = true) :
    (lastFlags k hk w).2 = true := by
  let o := observe k hk w
  let z := nativeSource k hk w
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let W := actualOriginalWord rate rewards C_star C_h z.val (nativeInvocation_launch rate rewards C_star C_h o.1 z)
  have hw : o.2.val.2.2.1 = some (RecordedQueueRun.run Q (W.take ((calendarBoundary t0 k hk).val - start z.val))) :=
    (calendarObservation_word rate rewards C_star C_h control0 b0 u0 t0 k hk w).1
  have hcurrent : (RecordedQueueRun.run Q (W.take ((calendarBoundary t0 k hk).val - start z.val))).overflow = false := by
    change o.2.val.2.2.1.any (fun S => !S.overflow) = true at hclear
    rw [hw, Option.any_some, Bool.not_eq_true'] at hclear
    exact hclear
  have hj : (calendarBoundary t0 k hk).val - start z.val ≤ W.length := by
    dsimp only [W]
    rw [actualOriginalWord_length, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    change t0.val + 1 + k - start z.val ≤ p.T - start z.val
    omega
  have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk w).1
  have hpast : (nativeBefore rate rewards C_star C_h control0 o.1 z).overflow = false := by
    change (nativeCell rate rewards C_star C_h control0 o.1 z ReferenceFirstLiveActualRefreshTestLaw.scalarZero).before.overflow = false
    rw [nativeCell_before_word]
    exact prefix_clear_mono rate W (o.1.val - start z.val) ((calendarBoundary t0 k hk).val - start z.val)
      (by exact Nat.sub_le_sub_right hdate.le _) hj hcurrent
  rw [calendarLastFlags_nativePreClear]
  change (prefixNumerical rate rewards C_star C_h o.1.castSucc z.val).any (fun S => !S.overflow) = true
  rw [nativeBefore_prefix rate rewards C_star C_h control0 o.1 z, Option.any_some, hpast]
  rfl

/-- The native clear flag on either actual current PRE-clear call section is
necessarily true; it was never identified with current PRE-clear by definition. -/
theorem calendarEndpointSection_native_clear (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hw : w ∈ sectionEvent renewed bs clear s k hk) : clear = true := by
  have hc : (observe k hk.le w).2.val.2.2.1.any (fun S => !S.overflow) = true := congrArg Prod.snd hw.2.2
  exact (congrArg Prod.snd hw.1.2).symm.trans
    (calendarLastFlags_clear_of_preClear rate rewards C_star C_h control0 b0 u0 t0 k hk.le w hc)

/-- No call uses the original complete assignment vector without a fibre
replacement; physical play is still represented by the produced extension. -/
theorem calendarExtensionKernel_noCall (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hc : sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = none) :
    extension k (by omega) w = Measure.dirac
      (ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)) := by
  change sourceCall ⟨t0.val + 1 + k, hk⟩ (observe k hk.le w).2.val.1.1.1.2 = none at hc
  rw [calendarExtensionKernel_apply, calendarVectorKernel_apply, nextVectorKernel_apply]
  simp only [installationSelection, hc]
  rfl

/-- An analytically stopped PRE state also keeps the original full vector,
including calls after the first overflow UPDATE. -/
theorem calendarExtensionKernel_preStopped (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hc : (pending k (by omega) w).2 = false) :
    extension k (by omega) w = Measure.dirac
      (ReferenceFirstCollectionRenewalVectorInsertion.av ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)) := by
  rw [calendarExtensionKernel_apply, calendarVectorKernel_apply]
  exact nextVectorKernel_of_preStopped rate rewards C_star C_h (t := (observe k hk.le w).1)
    (q := ⟨t0.val + 1 + k, hk⟩) control0
    ((observe k hk.le w).2.val, auxiliaryPair ⟨t0.val + 1 + k, hk⟩ (original k w).1.2) hc

omit b0 u0 t0 in
def taggedInstallationMass (q : Fin p.T) (x : TaggedPrefix rate q.castSucc × Auxiliary) : ℝ≥0∞ :=
  ReferenceNextInsertedSourceMarginal.installationMass rate rewards C_star C_h (t := x.1.1) q
    (x.1.2.val, auxiliaryPair q x.2)

omit b0 u0 t0 in
include control0 in
private theorem measurable_taggedInstallationMass (q : Fin p.T) :
    Measurable (taggedInstallationMass rate rewards C_star C_h q) := by
  apply measurable_sigma_prod_elim
  intro s
  exact (ReferenceNextInsertedSourceMarginal.measurable_installationMass rate rewards C_star C_h
    (t := s) q control0).comp ((measurable_subtype_coe.comp measurable_fst).prodMk
      ((measurable_auxiliaryPair q).comp measurable_snd))

/-- The support mass of the actual calendar installation request. No call
or a stopped PRE has no request and is kept as the literal zero branch. -/
def calendarInstallationMass (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) : ℝ≥0∞ :=
  taggedInstallationMass rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
    (observe k hk.le w, (original k w).1.2)

local notation "mass" => calendarInstallationMass rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarInstallationMass (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (mass k hk) := by
  exact (measurable_taggedInstallationMass rate rewards C_star C_h control0 ⟨t0.val + 1 + k, hk⟩).comp
    ((measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le).prodMk
      (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd)

private theorem calendarInstallationMass_onSection (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (w : Sample k) (hw : w ∈ sectionEvent renewed bs clear s k hk)
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w) = some (cutoff, theta)) :
    mass k hk w = AssignmentParameterFibreKernel.fibreMass p theta (chosen k hk theta w) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  have hc' : sourceCall q o.2.val.1.1.1.2 = some (cutoff, theta) := hc
  have hclear : preClearFlag rate (t := o.1) q o.2.val = true := congrArg Prod.snd hw.2.2
  change ReferenceNextInsertedSourceMarginal.installationMass rate rewards C_star C_h (t := o.1) q
    (o.2.val, auxiliaryPair q (original k w).1.2) = _
  simp only [ReferenceNextInsertedSourceMarginal.installationMass, installationSelection, hc', hclear, ite_true]
  rfl

/-- Positive support under the actual produced calendar measure, on either
literal call section. Retained positivity is transferred through the proved
raw-sample restoration law, rather than assumed about its incoming history. -/
theorem ae_calendarLaw_section_mass_pos (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    ∀ᵐ w ∂(law k hk.le).restrict (sectionEvent renewed bs clear s k hk), 0 < mass k hk w := by
  cases renewed with
  | true =>
      filter_upwards [ae_restrict_mem
        (measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk)] with w hw
      have hc : (sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)).isSome = true := hw.2.1
      obtain ⟨⟨cutoff, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hc
      rw [calendarInstallationMass_onSection rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk w hw cutoff theta hcall,
        calendarChosenEndpoint_onSection rate rewards C_star C_h control0 b0 u0 t0 true bs clear s k hk theta w hw]
      exact ReferenceNextInsertedSourceMarginal.freshEndpoint_mass_pos theta _
  | false =>
      let E := sectionEvent false bs clear s k hk
      let mu := (law k hk.le).restrict E
      let e := eraseBlock bs s k
      let r := fillBlock bs s k
      have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk
      have he := measurable_calendarEraseBlock rate rewards C_star C_h b0 u0 t0 bs s k
      have hr := measurable_calendarFillBlock rate rewards C_star C_h b0 u0 t0 bs s k
      have hsupport : ∀ᵐ w ∂mu.map e, w ∈ E := by
        apply (ae_map_iff he.aemeasurable hE).mpr
        filter_upwards [ae_restrict_mem hE] with w hw
        exact (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs w _).mpr hw
      have hinner : ∀ᵐ w ∂mu.map e, ∀ᵐ x ∂refreshAuxiliaryLaw bs s, 0 < mass k hk (r (w, x)) := by
        filter_upwards [hsupport] with w hw
        obtain ⟨cutoff, theta, hc, hpositive⟩ :=
          calendar_retained_refresh_support rate rewards C_star C_h control0 b0 u0 t0 bs clear s k hk w hw
        filter_upwards [hpositive (refreshSplit bs s (original k w).1.2).1] with x hx
        have hw' : r (w, x) ∈ E :=
          (calendarEndpointSection_withAuxiliary rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs w _).mpr hw
        have hz := (calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
          (fillBlockAuxiliary bs s ((original k w).1.2, x))).2
        have hc' : sourceCall ⟨t0.val + 1 + k, hk⟩ (current k hk.le (r (w, x))) = some (cutoff, theta) := by
          dsimp only [r, calendarFillBlock]
          rw [hz]
          exact hc
        rw [calendarInstallationMass_onSection rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk _ hw' cutoff theta hc',
          calendarChosenEndpoint_onSection rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk theta _ hw']
        exact hx
      have hset : MeasurableSet {w : Sample k | 0 < mass k hk w} :=
        measurableSet_lt measurable_const (measurable_calendarInstallationMass rate rewards C_star C_h control0 b0 u0 t0 k hk)
      have hprod := (Measure.ae_prod_iff_ae_ae (hset.preimage hr)).mpr hinner
      have hmap := (ae_map_iff hr.aemeasurable hset).mpr hprod
      rw [← calendarLaw_section_eq_restoreBlock rate rewards C_star C_h control0 b0 u0 t0 false bs clear s k hk hs] at hmap
      exact hmap

omit b0 u0 t0 in
def taggedFibreMatch (q : Fin p.T) (x : TaggedPrefix rate q.castSucc × (Auxiliary × Vector)) : Bool :=
  ReferenceNextInsertedSourceMarginal.fibreMatch rate rewards C_star C_h (t := x.1.1) q
    ((x.1.2.val, auxiliaryPair q x.2.1), x.2.2)

omit b0 u0 t0 in
include control0 in
private theorem measurable_taggedFibreMatch (q : Fin p.T) :
    Measurable (taggedFibreMatch rate rewards C_star C_h q) := by
  apply measurable_sigma_prod_elim
  intro s
  exact (ReferenceNextInsertedSourceMarginal.measurable_fibreMatch rate rewards C_star C_h (t := s) q control0).comp
    (((measurable_subtype_coe.comp measurable_fst).prodMk
      ((measurable_auxiliaryPair q).comp measurable_snd.fst)).prodMk measurable_snd.snd)

/-- Borel graph test for the actual requested sampler fibre. No request
(no call or PRE-stopped) imposes no equality on an arbitrary vector. -/
def calendarFibreMatch (k : ℕ) (hk : t0.val + 1 + k < p.T) (wv : Sample k × Vector) : Bool :=
  taggedFibreMatch rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
    (observe k hk.le wv.1, ((original k wv.1).1.2, wv.2))

local notation "matches" => calendarFibreMatch rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarFibreMatch (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (matches k hk) := by
  exact (measurable_taggedFibreMatch rate rewards C_star C_h control0 ⟨t0.val + 1 + k, hk⟩).comp
    (((measurable_calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp
      measurable_fst).prodMk (((measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd.comp
        measurable_fst).prodMk measurable_snd))

/-- The actual newly sampled full vector lies in the requested fibre almost
everywhere under the produced call-section law. This is not pointwise agreement
for arbitrary vectors, and null/failure/none branches remain in the kernel. -/
theorem ae_calendarLaw_section_fibreMatch (renewed bs clear : Bool) (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val < t0.val + 1 + k) :
    ∀ᵐ wv ∂(law (k + 1) (by omega)).restrict
      (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk), matches k hk wv = true := by
  have hE := measurableSet_calendarEndpointSection rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk
  change ∀ᵐ wv ∂((law k hk.le).compProd (extension k (by omega))).restrict
    (Prod.fst ⁻¹' sectionEvent renewed bs clear s k hk), matches k hk wv = true
  rw [compProd_restrict_fst _ _ _ hE]
  apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun
    (measurable_calendarFibreMatch rate rewards C_star C_h control0 b0 u0 t0 k hk) measurable_const)
  filter_upwards [ae_calendarLaw_section_mass_pos rate rewards C_star C_h control0 b0 u0 t0 renewed bs clear s k hk hs]
    with w hw
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o : TaggedPrefix rate q.castSucc := observe k hk.le w
  let i : NextInput rate o.1 q := (o.2.val, auxiliaryPair q (original k w).1.2)
  cases hsel : installationSelection rate rewards C_star C_h (t := o.1) q i with
  | none =>
      exact Filter.Eventually.of_forall fun v => by
        change ReferenceNextInsertedSourceMarginal.fibreMatch rate rewards C_star C_h (t := o.1) q (i, v) = true
        simp only [ReferenceNextInsertedSourceMarginal.fibreMatch, hsel]
  | some a =>
      change 0 < ReferenceNextInsertedSourceMarginal.installationMass rate rewards C_star C_h (t := o.1) q i at hw
      rw [ReferenceNextInsertedSourceMarginal.installationMass, hsel] at hw
      have hkernel : extension k (by omega) w = AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2 := by
        rw [calendarExtensionKernel_apply, calendarVectorKernel_apply, nextVectorKernel_apply]
        change (match installationSelection rate rewards C_star C_h (t := o.1) q i with
          | none => _ | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2) = _
        rw [hsel]
      rw [hkernel]
      filter_upwards [AssignmentParameterFibreKernel.ae_successfulSlowSet_eq_of_fibreMass_pos p a.1 a.2 hw] with v hv
      change ReferenceNextInsertedSourceMarginal.fibreMatch rate rewards C_star C_h (t := o.1) q (i, v) = true
      simp only [ReferenceNextInsertedSourceMarginal.fibreMatch, hsel, hv, decide_true]

end Bandits.Support.ReferenceGeneratedCalendarEndpointMixture
