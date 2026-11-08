/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability
public import Bandits.Support.ReferenceCorrectedLaunchMeasurability
public import Bandits.Support.ReferenceCompletePhysicalHistory

/-!
# Generated-source second-DOWN-completion ambiguity event

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-55,74-124`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-46`.

For a source-generated crossing and its actual physical start, this module
adapts the admitted corrected launch and the complete original-row physical
suffix to the existing active-horizon DOWN event. The total event is a finite
union over physical starts and exact second-completion prefixes. It is an
internal Borel event, not source `E_amb`, global decoder failure, or a
probability bound.

The launch state, original complete rows, selected private row index, whole
grid reward table, actual initial bank, and all runtime diagnostics are kept.
No success, no-dagger, seed-measurability, service, or source-law premise is
added. No manuscript theorem or section is closed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

universe u

namespace Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev ActiveRunInput (p : Parameters) (rate : RateInput p) (s : ℕ) :=
  ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s

variable {p : Parameters} {rate : RateInput p}

/-- The genuine crossing fibre at physical start `s`, on the original source
carrier with every private coordinate still present. -/
def generatedLaunchFiberSet
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) : Set (SourceInput p) :=
  {source |
    (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome = true ∧
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s}

/-- The source points whose actual generated crossing has elapsed time `s`.
This subtype carries the genuine subspace measurable structure. -/
abbrev GeneratedLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :=
  {source : SourceInput p // source ∈ generatedLaunchFiberSet (rate := rate)
    rewards C_star C_h s}

/-- The launch-start fibre is Borel by the admitted generated-boundary
measurability theorem. -/
theorem measurableSet_generatedLaunchFiberSet
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :
    MeasurableSet (generatedLaunchFiberSet (rate := rate) rewards C_star C_h s) := by
  simpa [generatedLaunchFiberSet, ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput] using
      ReferenceCorrectedLaunchMeasurability.measurableSet_generated_launch_start_fiber
        rate rewards C_star C_h s

private theorem generatedLaunch_isSome
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s) :
    (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source.1 rewards C_star C_h).isSome = true := by
  apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source.1 rewards C_star C_h).2
  simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput] using source.2.1

/-- Every source in the genuine crossing fibre has an actual corrected
launch option. -/
theorem generatedLaunch_ne_none
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source.1 rewards C_star C_h ≠ none :=
  Option.ne_none_iff_isSome.mpr
    (generatedLaunch_isSome (rate := rate) rewards C_star C_h s source)

private def generatedLaunchOptionCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s) :
    Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) :=
  (ReferenceCorrectedInitializationLaunch.correctedLaunch
    rate source.1 rewards C_star C_h).map
      (ReferenceActivePhysicalStepMeasurability.encodeState (p := p) (rate := rate))

private theorem generatedLaunchOptionCode_isSome
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s) :
    (generatedLaunchOptionCode (rate := rate) rewards C_star C_h s source).isSome = true := by
  simp [generatedLaunchOptionCode, generatedLaunch_isSome]

private def generatedLaunchStateCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s) : ReferenceActivePhysicalStepMeasurability.StateCode p rate :=
  (generatedLaunchOptionCode (rate := rate) rewards C_star C_h s source).get
    (generatedLaunchOptionCode_isSome (rate := rate) rewards C_star C_h s source)

private theorem option_get_mem_iff_sum_inl
    {α : Type u} (o : Option α) (ho : o.isSome = true) (set : Set α) :
    o.get ho ∈ set ↔ Equiv.optionEquivSumPUnit.{u, u} α o ∈ Sum.inl '' set := by
  cases o with
  | none => simp at ho
  | some a => simp [Equiv.optionEquivSumPUnit]

private theorem measurable_option_get_of_isSome
    {Ω : Type*} {α : Type u} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → Option α) (hf : Measurable f)
    (hsome : ∀ x, (f x).isSome = true) :
    Measurable (fun x => (f x).get (hsome x)) := by
  let optionSumEquiv : Option α ≃ α ⊕ PUnit.{u+1} :=
    Equiv.optionEquivSumPUnit.{u, u} α
  have hsum : Measurable (fun x => optionSumEquiv (f x)) := by
    change Measurable (fun x => Equiv.optionEquivSumPUnit.{u, u} α (f x))
    exact measurable_comap_iff.mp hf
  intro u hu
  have hsumset : MeasurableSet ((Sum.inl : α → α ⊕ PUnit.{u+1}) '' u) :=
    MeasurableSet.inl_image hu
  have hpre := hsum hsumset
  have hpreEq : (fun x => (f x).get (hsome x)) ⁻¹' u =
      (fun x => optionSumEquiv (f x)) ⁻¹' (Sum.inl '' u) := by
    ext x
    exact option_get_mem_iff_sum_inl (f x) (hsome x) u
  rw [hpreEq]
  exact hpre

private theorem measurable_generatedLaunchStateCode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :
    Measurable (generatedLaunchStateCode (rate := rate) rewards C_star C_h s) := by
  apply measurable_option_get_of_isSome
  · exact (ReferenceCorrectedLaunchMeasurability.measurable_correctedLaunch_encodeState
      rate rewards C_star C_h).comp measurable_subtype_coe

private theorem generatedLaunchStateCode_eq_payload
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s) :
    generatedLaunchStateCode (rate := rate) rewards C_star C_h s source =
      ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
          C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source)) := by
  have hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate source.1 rewards C_star C_h
      (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source)
  cases hopt : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source.1 rewards C_star C_h with
  | none => exact (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source hopt).elim
  | some actual =>
      simp [generatedLaunchStateCode, generatedLaunchOptionCode, hopt,
        ReferenceCompletePhysicalHistory.correctedLaunchPayload]

/-- The actual corrected launch payload, original complete rows, original
selected private index, and whole grid rewards, restricted only by the
existing all-active-at-start condition. -/
def generatedActiveRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ)
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s) :
    ActiveRunInput p rate s := by
  let hnone := generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source
  let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
    rate source.1 rewards C_star C_h hnone
  let hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate source.1 rewards C_star C_h hnone
  refine ⟨(active, (source.1.1.2,
    (ActualInitializationPhysicalStep.selectedRowIndex p source.1, rewards))), ?_⟩
  intro j
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate source.1 rewards C_star C_h active hlaunch
  have hstart := source.2.2
  have hmodej := hmode j
  simpa [hstart] using hmodej

/-- The source-generated active-run input has the literal requested product
coordinates. -/
theorem generatedActiveRunInput_val
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ)
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s) :
    (generatedActiveRunInput (rate := rate) rewards C_star C_h s source).val =
      (ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
        C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source),
        (source.1.1.2,
        (ActualInitializationPhysicalStep.selectedRowIndex p source.1, rewards))) := by
  unfold generatedActiveRunInput
  rfl

/-- The active-run input adapter is Borel in the existing state-code comap
space, retaining the complete original rows and selected index. -/
theorem measurable_generatedActiveRunInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :
    Measurable (generatedActiveRunInput (rate := rate) rewards C_star C_h s) := by
  have hsource : Measurable (fun source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s => source.1) := measurable_subtype_coe
  have hpayload : Measurable (fun source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s =>
      ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
        C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source)) := by
    have heq :
        (fun source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s =>
          ReferenceActivePhysicalStepMeasurability.encodeState
            (ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
              C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source))) =
        generatedLaunchStateCode (rate := rate) rewards C_star C_h s := by
      funext source
      exact (generatedLaunchStateCode_eq_payload
        (rate := rate) rewards C_star C_h s source).symm
    apply measurable_comap_iff.mpr
    change Measurable (fun source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s =>
      ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
          C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source)))
    rw [heq]
    exact measurable_generatedLaunchStateCode (rate := rate) rewards C_star C_h s
  have hrows : Measurable (fun source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s => source.1.1.2) :=
    (measurable_snd.comp measurable_fst).comp hsource
  have hselectedBase : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hselected : Measurable (fun source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s => ActualInitializationPhysicalStep.selectedRowIndex p source.1) :=
    hselectedBase.comp hsource
  have hdata : Measurable (fun source : GeneratedLaunchFiber (rate := rate)
      rewards C_star C_h s =>
      (ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
          C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source),
        (source.1.1.2, (ActualInitializationPhysicalStep.selectedRowIndex p source.1,
          rewards)))) :=
    hpayload.prodMk (hrows.prodMk (hselected.prodMk measurable_const))
  unfold generatedActiveRunInput
  exact hdata.subtype_mk

/-- The completed DOWN event pulled back to the exact generated crossing
fibre. Its carrier is the genuine original-source subtype. -/
def generatedSecondDownAmbiguityOnLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T) (i : Fin (p.m - 1)) :
    Set (GeneratedLaunchFiber (rate := rate) rewards C_star C_h s) :=
  (generatedActiveRunInput (rate := rate) rewards C_star C_h s) ⁻¹'
    ReferenceDownCompletedAmbiguityMeasurability.secondDownAmbiguityEvent
      (p := p) (rate := rate) s n span i

/-- The subtype pullback is Borel by the admitted actual-run event theorem and
the actual generated launch adapter. -/
theorem measurableSet_generatedSecondDownAmbiguityOnLaunchFiber
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T) (i : Fin (p.m - 1)) :
    MeasurableSet (generatedSecondDownAmbiguityOnLaunchFiber
      (rate := rate) rewards C_star C_h s n span i) := by
  exact (ReferenceDownCompletedAmbiguityMeasurability.measurableSet_secondDownAmbiguityEvent
    (p := p) (rate := rate) s n span i).preimage
      (measurable_generatedActiveRunInput (rate := rate) rewards C_star C_h s)

/-- The pulled-back event is exactly D's complete runtime event on the
source-generated `n`-prefix. -/
theorem mem_generatedSecondDownAmbiguityOnLaunchFiber_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T) (i : Fin (p.m - 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s) :
    source ∈ generatedSecondDownAmbiguityOnLaunchFiber
      (rate := rate) rewards C_star C_h s n span i ↔
    generatedActiveRunInput (rate := rate) rewards C_star C_h s source ∈
      ReferenceDownCompletedAmbiguityMeasurability.secondDownAmbiguityEvent
        (p := p) (rate := rate) s n span i := Iff.rfl

/-- The ambient original-source event for one physical start and one exact
second-completion prefix. -/
def generatedSecondDownAmbiguityPrefixEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T) (i : Fin (p.m - 1)) :
    Set (SourceInput p) :=
  Subtype.val '' generatedSecondDownAmbiguityOnLaunchFiber
    (rate := rate) rewards C_star C_h s n span i

/-- Ambient membership records the exact crossing fibre and D's runtime event
on the actual input adapted from that same source. -/
theorem mem_generatedSecondDownAmbiguityPrefixEvent_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T) (i : Fin (p.m - 1))
    (source : SourceInput p) :
    source ∈ generatedSecondDownAmbiguityPrefixEvent
      (rate := rate) rewards C_star C_h s n span i ↔
    ∃ hsource : source ∈ generatedLaunchFiberSet (rate := rate) rewards C_star C_h s,
      generatedActiveRunInput (rate := rate) rewards C_star C_h s ⟨source, hsource⟩ ∈
        ReferenceDownCompletedAmbiguityMeasurability.secondDownAmbiguityEvent
          (p := p) (rate := rate) s n span i := by
  constructor
  · rintro ⟨subsource, hmem, hval⟩
    cases hval
    exact ⟨subsource.2, hmem⟩
  · rintro ⟨hsource, hevent⟩
    exact ⟨⟨source, hsource⟩, hevent, rfl⟩

/-- Every exact zero-length generated prefix is empty by D's zero-horizon
theorem, while its adapter retains the actual launch state and bank. -/
theorem not_mem_generatedSecondDownAmbiguityOnLaunchFiber_zero
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (span : s + 0 ≤ p.T) (i : Fin (p.m - 1))
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s) :
    source ∉ generatedSecondDownAmbiguityOnLaunchFiber
      (rate := rate) rewards C_star C_h s 0 span i := by
  have hz := ReferenceDownCompletedAmbiguityMeasurability.zero_horizon
    (p := p) (rate := rate) s span i
      (generatedActiveRunInput (rate := rate) rewards C_star C_h s source)
  exact hz.2.2

/-- The ambient event for one zero-length source prefix is empty. -/
theorem not_mem_generatedSecondDownAmbiguityPrefixEvent_zero
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (span : s + 0 ≤ p.T) (i : Fin (p.m - 1))
    (source : SourceInput p) :
    source ∉ generatedSecondDownAmbiguityPrefixEvent
      (rate := rate) rewards C_star C_h s 0 span i := by
  intro hmem
  obtain ⟨hsource, hevent⟩ :=
    (mem_generatedSecondDownAmbiguityPrefixEvent_iff
      (rate := rate) rewards C_star C_h s 0 span i source).mp hmem
  exact not_mem_generatedSecondDownAmbiguityOnLaunchFiber_zero
    (rate := rate) rewards C_star C_h s span i ⟨source, hsource⟩ hevent

/-- Each ambient prefix event is Borel by the measurable subtype embedding of
the original generated crossing fibre. -/
theorem measurableSet_generatedSecondDownAmbiguityPrefixEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T) (i : Fin (p.m - 1)) :
    MeasurableSet (generatedSecondDownAmbiguityPrefixEvent
      (rate := rate) rewards C_star C_h s n span i) :=
  MeasurableSet.subtype_image
    (measurableSet_generatedLaunchFiberSet (rate := rate) rewards C_star C_h s)
    (measurableSet_generatedSecondDownAmbiguityOnLaunchFiber
      (rate := rate) rewards C_star C_h s n span i)

/-- For every generated crossing, the computed `n`-prefix records are the
first `n` records of C's already constructed complete physical suffix. -/
private theorem records_foldl_extension
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    ∃ tail, (entries.foldl
      (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start mode)
      acc).records = acc.records ++ tail := by
  induction entries generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons entry rest ih =>
      obtain ⟨tail, htail⟩ := ih
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards start mode acc entry)
      let input := ReferenceActivePhysicalHorizon.roundInputAt
        initial rows selected rewards start mode acc entry
      refine ⟨[⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] ++ tail, ?_⟩
      rw [List.foldl_cons, htail]
      have hfold :
          (ReferenceActivePhysicalHorizon.foldRound
            initial rows selected rewards start mode acc entry).records =
            acc.records ++ [⟨input, ReferenceActivePhysicalStep.step input, rfl⟩] := by
        rfl
      rw [hfold]
      simp only [List.append_assoc]

theorem generatedRun_records_eq_completeSuffixRecords_take
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s n : ℕ) (span : s + n ≤ p.T)
    (source : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s) :
    (ReferenceActiveHorizonMeasurability.runOfInput
      (p := p) (rate := rate) s n span
      (generatedActiveRunInput (rate := rate) rewards C_star C_h s source)).records =
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source.1 rewards C_star C_h).take n := by
  let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source.1 rewards
    C_star C_h (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source)
  let launch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate source.1 rewards C_star C_h
      (generatedLaunch_ne_none (rate := rate) rewards C_star C_h s source)
  let rows := source.1.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source.1
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source.1 rewards C_star C_h = s :=
    source.2.2
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s :=
    by simpa [hstart] using
      ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source.1 rewards C_star C_h active launch
  have hrunRecords :
      (ReferenceActiveHorizonMeasurability.runOfInput
        (p := p) (rate := rate) s n span
        (generatedActiveRunInput (rate := rate) rewards C_star C_h s source)).records =
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode).records := by
    simp only [ReferenceActiveHorizonMeasurability.runOfInput, generatedActiveRunInput]
    rfl
  have hremaining : n + (p.T - s - n) = p.T - s := by omega
  have hlongspan : s + (n + (p.T - s - n)) ≤ p.T := by omega
  have happend := ReferenceActivePhysicalHorizon.run_append active rows selected rewards
    s n (p.T - s - n) hlongspan hmode
  have happend' :
      ReferenceActivePhysicalHorizon.run active rows selected rewards s (p.T - s)
        (by omega) hmode =
        ReferenceActivePhysicalHorizon.foldCalendar active rows selected rewards s (s + n)
          (p.T - s - n) (by omega) (by omega) hmode
          (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode) := by
    simpa [hremaining] using happend
  have hcomplete := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source.1 rewards C_star C_h active launch
  have hcomplete' :
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h =
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s (p.T - s)
          (by omega) hmode).records := by
    simpa only [hstart] using hcomplete
  have htail := records_foldl_extension active rows selected rewards s hmode
    (ReferenceActivePhysicalHorizon.calendarEntries s (s + n) (p.T - s - n)
      (by omega) (by omega))
    (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode)
  obtain ⟨tail, htail⟩ := htail
  have hfullrecords :
      (ReferenceActivePhysicalHorizon.run active rows selected rewards s (p.T - s)
        (by omega) hmode).records =
        (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode).records ++ tail := by
    calc
      _ = (ReferenceActivePhysicalHorizon.foldCalendar active rows selected rewards s (s + n)
            (p.T - s - n) (by omega) (by omega) hmode
            (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode)).records :=
          congrArg ReferenceActivePhysicalHorizon.Run.records happend'
      _ = _ := by simpa [ReferenceActivePhysicalHorizon.foldCalendar] using htail
  have hlength := ReferenceActivePhysicalHorizon.run_record_count
    active rows selected rewards s n span hmode
  rw [hrunRecords]
  calc
    (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode).records =
        ((ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode).records ++ tail).take n := by
          let prefixRecords :=
            (ReferenceActivePhysicalHorizon.run active rows selected rewards s n span hmode).records
          have hprefixLength : prefixRecords.length = n := hlength
          have hprefixSelf : prefixRecords.take n = prefixRecords := by
            rw [← hprefixLength]
            simp
          have htake := List.take_append_of_le_length
            (l₁ := prefixRecords) (l₂ := tail) (i := n) (by omega)
          change prefixRecords = (prefixRecords ++ tail).take n
          rw [htake, hprefixSelf]
    _ = (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source.1 rewards C_star C_h).take n := by
          rw [← hfullrecords, ← hcomplete']

/-- The total internal source event ranges over every actual generated
physical start and every exact prefix ending no later than `T`. -/
def generatedSecondDownAmbiguityEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  ⋃ s : Fin (p.T + 1), ⋃ n : Fin (p.T - s.val + 1),
    generatedSecondDownAmbiguityPrefixEvent (rate := rate) rewards C_star C_h
      s.val n.val (by omega) i

/-- Exact existential characterization of the total generated-prefix event,
with both physical indices and the D runtime condition visible. -/
theorem mem_generatedSecondDownAmbiguityEvent_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (source : SourceInput p) :
    source ∈ generatedSecondDownAmbiguityEvent (rate := rate) rewards C_star C_h i ↔
      ∃ s : Fin (p.T + 1), ∃ n : Fin (p.T - s.val + 1),
        ∃ hsource : source ∈ generatedLaunchFiberSet (rate := rate) rewards C_star C_h s.val,
          generatedActiveRunInput (rate := rate) rewards C_star C_h s.val
            ⟨source, hsource⟩ ∈
            ReferenceDownCompletedAmbiguityMeasurability.secondDownAmbiguityEvent
              (p := p) (rate := rate) s.val n.val (by omega) i := by
  constructor
  · intro h
    simp only [generatedSecondDownAmbiguityEvent, Set.mem_iUnion] at h
    rcases h with ⟨s, n, hprefix⟩
    obtain ⟨hsource, hevent⟩ :=
      (mem_generatedSecondDownAmbiguityPrefixEvent_iff
        (rate := rate) rewards C_star C_h s.val n.val (by omega) i source).mp hprefix
    exact ⟨s, n, hsource, hevent⟩
  · rintro ⟨s, n, hsource, hevent⟩
    simp only [generatedSecondDownAmbiguityEvent, Set.mem_iUnion]
    exact ⟨s, n,
      (mem_generatedSecondDownAmbiguityPrefixEvent_iff
        (rate := rate) rewards C_star C_h s.val n.val (by omega) i source).mpr
        ⟨hsource, hevent⟩⟩

/-- The total source event is Borel as a finite union of the Borel
source-generated exact-prefix events. -/
theorem measurableSet_generatedSecondDownAmbiguityEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    MeasurableSet (generatedSecondDownAmbiguityEvent
      (rate := rate) rewards C_star C_h i) := by
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_generatedSecondDownAmbiguityPrefixEvent
    (rate := rate) rewards C_star C_h s.val n.val (by omega) i

/-- The total event is false on source exhaustion, and the existing complete
physical suffix is empty there. -/
theorem generatedSecondDownAmbiguityEvent_false_of_no_crossing
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    source ∉ generatedSecondDownAmbiguityEvent (rate := rate) rewards C_star C_h i ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
  constructor
  · intro hevent
    obtain ⟨s, n, hsource, _⟩ :=
      (mem_generatedSecondDownAmbiguityEvent_iff
        (rate := rate) rewards C_star C_h i source).mp hevent
    have hsome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mpr (by
        simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hsource.1)
    rw [hlaunch] at hsome
    cases hsome
  · exact (ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate source rewards C_star C_h hlaunch).2.1

/-- A terminal crossing keeps the real corrected payload and has an empty
physical suffix; its event is false because only the zero-length prefix can
occur, which D proves empty on the actual final state. -/
theorem generatedSecondDownAmbiguityEvent_false_of_terminal_crossing
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (source : SourceInput p)
    (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = p.T) :
    source ∉ generatedSecondDownAmbiguityEvent (rate := rate) rewards C_star C_h i ∧
      ReferenceCompletePhysicalHistory.correctedLaunchPayload rate source rewards C_star C_h
        (by rw [hlaunch]; simp) = active ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h = [] := by
  have hhistory := ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
    rate source rewards C_star C_h active hlaunch hterminal
  refine ⟨?_, ?_, hhistory.1⟩
  · intro hevent
    obtain ⟨s, n, hsource, hevent⟩ :=
      (mem_generatedSecondDownAmbiguityEvent_iff
        (rate := rate) rewards C_star C_h i source).mp hevent
    have hstart : s.val = p.T := hsource.2.symm.trans hterminal
    have hnval : n.val = 0 := by
      omega
    have hn : n = 0 := Fin.ext hnval
    let fiber : GeneratedLaunchFiber (rate := rate) rewards C_star C_h s.val :=
      ⟨source, hsource⟩
    have hspan0 : s.val + 0 ≤ p.T := by omega
    have hz := ReferenceDownCompletedAmbiguityMeasurability.zero_horizon
      (p := p) (rate := rate) s.val hspan0 i
        (generatedActiveRunInput (rate := rate) rewards C_star C_h s.val fiber)
    have hevent0 :
        generatedActiveRunInput (rate := rate) rewards C_star C_h s.val fiber ∈
          ReferenceDownCompletedAmbiguityMeasurability.secondDownAmbiguityEvent
            (p := p) (rate := rate) s.val 0 hspan0 i := by
      subst n
      simpa [fiber] using hevent
    exact hz.2.2 hevent0
  · exact Option.some.inj ((ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
      rate source rewards C_star C_h (by rw [hlaunch]; simp)).symm.trans hlaunch)

end Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability

end
