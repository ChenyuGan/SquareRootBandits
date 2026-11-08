/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison
public import Bandits.Support.DeferredRefreshUniformEvaluator

/-!
# Actual original collection prefixes for hidden refreshes

The original source supplies the unique numerical word, old anchor and trigger.
The sampled path uses disjoint analytical entries. Its source-varying evaluator,
literal prefix cell, and restricted finite-path tests are Borel, with the joint
source-times-array law proved below. Replacement locality, the real corrected
endpoint formula and the actual fibre join remain open. No all-rank coupling
or manuscript closure is claimed.

Sources: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:176-215,323-366`, and
`appendix_a_local_protocol.tex:28-79` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix

namespace Bandits.Support.ReferenceActualCollectionHiddenRefreshPath

open _root_.Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open _root_.Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open _root_.Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds (AuxiliaryArray auxiliaryUniformLaw)
open _root_.Bandits.Support.DeferredRefreshUniformEvaluator (PrefixCoordinates)
open _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell (queueParameters)
open _root_.Bandits.Support.ReferenceFirstCorrectedNextCalendarWordJoin (calendarReplay)
open _root_.Bandits.Support.ReferenceCompleteSuffixInputMeasurability (IndexedSource
  actualRoundInputAt measurable_actualRoundInputAt measurableSet_indexDomain
  measurable_physicalStart)
open _root_.Bandits.Support.ReferenceFirstLiveCoordinatorStepMeasurability (LiveInput liveSet
  measurableSet_liveSet live_state liveRegisters liveOwned liveBase liveCoordinates
  measurable_liveCoordinates measurable_livePayload measurable_liveCode)
open _root_.Bandits.Support.ReferenceCollectionOutcomeMeasurability (FullObservation
  canonicalCollectionFullObservation measurable_canonicalCollectionFullObservation optionalElim
  measurable_optionalElim collectionFullObservation collectionTag_eq_actual outcomeTag
  canonicalCollectionFullObservation_collection canonicalCollectionFullObservation_invalid
  canonicalCollectionFullObservation_absent)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)

variable {p : ConstructorDimensions.Parameters}

section OriginalWord

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)
  (hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
    rate z rewards C_star C_h = some active)

include hlaunch

/-- Existence and uniqueness of the actual complete numerical word on the
genuine corrected-launch branch. -/
theorem existsUnique_actualOriginalWord :
    ∃! L : List (RecordedQueueRun.RoundInput p.K),
      prefixInputs rate rewards C_star C_h p.T z = some L := by
  obtain ⟨active, hactive⟩ := hlaunch
  have hrestore :=
    ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
      rate rewards C_star C_h z
  rw [hactive] at hrestore
  obtain ⟨L, _hlen, _hprefix, hfull, hunique, _⟩ := hrestore
  refine ⟨L, hfull, ?_⟩
  intro L' hL'
  exact hunique L' hL'

/-- The unique word, defined only on the actual corrected-launch event. -/
def actualOriginalWord :
    List (RecordedQueueRun.RoundInput p.K) :=
  (existsUnique_actualOriginalWord rate rewards C_star C_h z hlaunch).exists.choose

/-- The chosen word is exactly the actual complete source prefix. -/
theorem actualOriginalWord_spec :
    prefixInputs rate rewards C_star C_h p.T z =
      some (actualOriginalWord rate rewards C_star C_h z hlaunch) :=
  (existsUnique_actualOriginalWord rate rewards C_star C_h z hlaunch).exists.choose_spec

/-- Its length is the actual complete-suffix record count. -/
theorem actualOriginalWord_length :
    (actualOriginalWord rate rewards C_star C_h z hlaunch).length =
      (completeSuffixRecords rate z rewards C_star C_h).length := by
  have hrestore :=
    ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
      rate rewards C_star C_h z
  rw [Classical.choose_spec hlaunch] at hrestore
  obtain ⟨L, hlen, _hprefix, hfull, _hunique, _⟩ := hrestore
  have hsame : L = actualOriginalWord rate rewards C_star C_h z hlaunch :=
    Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z hlaunch))
  simpa only [hsame] using hlen

/-- Every calendar prefix is the matching prefix of the same unique actual word. -/
theorem actualOriginalWord_prefix
    (n : ℕ)
    (hn : n ≤ (completeSuffixRecords rate z rewards C_star C_h).length) :
    prefixInputs rate rewards C_star C_h (physicalStart rate z rewards C_star C_h + n) z =
      some ((actualOriginalWord rate rewards C_star C_h z hlaunch).take n) := by
  have hrestore :=
    ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
      rate rewards C_star C_h z
  rw [Classical.choose_spec hlaunch] at hrestore
  obtain ⟨L, _hlen, hprefix, hfull, _hunique, _⟩ := hrestore
  have hsame : L = actualOriginalWord rate rewards C_star C_h z hlaunch :=
    Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z hlaunch))
  simpa only [hsame] using hprefix n hn

/-- The actual queue registers, weights and slow marginals use the same word
and the accepted first-overflow cut. -/
theorem actualOriginalWord_numericalPrefix
    (n : ℕ)
    (hn : n ≤ (actualOriginalWord rate rewards C_star C_h z hlaunch).length) :
    let L := actualOriginalWord rate rewards C_star C_h z hlaunch
    let Q := queueParameters rate
    let base := AssignmentScoreReconstruction.sourceWeightBase p
    let cut := min n (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L)
    (∀ i, (RecordedQueueRun.run Q (L.take n)).registers i = calendarReplay rate L i cut) ∧
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (L.take n)) =
        (fun i => base ^ (calendarReplay rate L i cut).1) ∧
      (fun i => RecordedQueueSummation.runMarginal Q p.m L n i) =
        ProductSetLaw.theta p.m (fun i => base ^ (calendarReplay rate L i cut).1) := by
  have hactive := Classical.choose_spec hlaunch
  have hrestore :=
    ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
      rate rewards C_star C_h z
  rw [hactive] at hrestore
  obtain ⟨L, _hlen, _hprefix, hfull, _hunique, _hbirths, _hcollections, hstates⟩ :=
    hrestore
  have hsame : L = actualOriginalWord rate rewards C_star C_h z hlaunch :=
    Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z hlaunch))
  subst L
  have hstate := hstates n hn
  exact ⟨hstate.1, hstate.2.1, hstate.2.2.1⟩

end OriginalWord

/-- The literal cutoff-prefix event before the old boundary, with actual
pre-round nonoverflow and no future-invocation test. -/
def collectionPrefixCell
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (e b : ℕ) :
    Set (SourceInput p) :=
  {z | let R := completeSuffixRecords rate z rewards C_star C_h
    let s := physicalStart rate z rewards C_star C_h
    e ≤ b ∧ b ≤ R.length ∧ ∃ he : e < R.length, match R[e].input.state.coordinator with
      | .live r _ _ =>
          ReferenceCollectionPhaseHistory.cutoffChosen R[e].input = true ∧
          s + b + 1 < r.gridBoundary ∧ (∀ k : Fin R.length, e < k.val → k.val < b →
            ReferenceCollectionPhaseHistory.laterChosen R[k.val].input = false) ∧
          ∃ o, prefixReadout rate rewards C_star C_h (s + b) z = some o ∧ o.2.1 = false
      | _ => False}

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (e b : ℕ)

variable (z : SourceInput p)
  (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b)

local notation "records" => completeSuffixRecords rate z rewards C_star C_h
local notation "start" => physicalStart rate z rewards C_star C_h

/-- The actual incoming old payload, retaining absence on every other branch. -/
def cutoffPayload? :
    Option (ReferenceActivePhysicalStep.Payload rate) :=
  ((records)[e]?).bind fun record =>
    match record.input.state.coordinator with
    | .live r _ _ => some r.payload
    | _ => none

/-- Unpack only the actual incoming LIVE constructor on the literal cell. -/
theorem collectionPrefixCell_live
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    ∃ (he : e < (records).length) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
      (records)[e].input.state.coordinator = .live r q base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen (records)[e].input = true ∧
      start + b + 1 < r.gridBoundary ∧
      cutoffPayload? rate rewards C_star C_h e z = some r.payload := by
  obtain ⟨_, _, he, hcell⟩ := hz
  cases hc : (records)[e].input.state.coordinator with
  | live r q base =>
      rw [hc] at hcell
      refine ⟨he, r, q, base, hc, hcell.1, hcell.2.1, ?_⟩
      simp only [cutoffPayload?, List.getElem?_eq_getElem he, Option.bind_some, hc]
  | first => simp only [hc] at hcell
  | collection P ledger saved => simp only [hc] at hcell
  | dagger => simp only [hc] at hcell

/-- Cell membership itself entails an actual corrected launch. -/
theorem collectionPrefixCell_launch
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active := by
  obtain ⟨he, _⟩ := hz.2.2
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      have hnil := (no_launch_complete_history rate z rewards C_star C_h hl).2.1
      rw [hnil] at he
      simp only [List.length_nil, Nat.not_lt_zero] at he
  | some active => exact ⟨active, rfl⟩

/-- The unique actual payload, without a value on an absent cell. -/
def oldPayload :
    ReferenceActivePhysicalStep.Payload rate :=
  (cutoffPayload? rate rewards C_star C_h e z).get (by
    obtain ⟨_, _, _, _, _, _, _, hp⟩ :=
      collectionPrefixCell_live rate rewards C_star C_h e b z hz
    rw [hp]
    rfl)

/-- The payload getter is exactly the payload stored at the actual cutoff. -/
theorem oldPayload_eq
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hP : cutoffPayload? rate rewards C_star C_h e z = some P) :
    oldPayload rate rewards C_star C_h e b z hz = P := by
  unfold oldPayload
  simp only [hP, Option.get_some]

/-- A past installation supplies the actual old anchor and its entire birth
score vector, without a later-invocation premise. -/
theorem collectionPrefixCell_anchor_origin :
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate) (scores : Fin p.K → ℕ),
      birth ∈ (records).take e ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      ReferenceCompleteEpisodeAnchorOrigin.IsEpisodeAnchorBirth birth ∧
      ReferenceCompleteLiveComplementScoreSpan.installationScoreVector birth P scores ∧
      birth.input.time = P.sigma ∧ (oldPayload rate rewards C_star C_h e b z hz).anchor = P.anchor ∧
      (∀ a, P.anchor a = AssignmentScoreReconstruction.sourceWeightBase p ^ scores a) := by
  obtain ⟨he, r, q, base, hlive, _, _, hp⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e b z hz
  obtain ⟨birth, P, scores, hb, hi, ha, hs, ht, _, hanchor, hweights, _⟩ :=
    ReferenceCompleteEpisodeAnchorOrigin.complete_live_episode_anchor_origin
      rate rewards C_star C_h z ⟨e, he⟩ r q base hlive
  refine ⟨birth, P, scores, hb, hi, ha, hs, ht, ?_, hweights⟩
  rw [oldPayload_eq rate rewards C_star C_h e b z hz r.payload hp]
  exact hanchor

/-- An actual LIVE cutoff has a preceding triggering update. -/
theorem collectionPrefixCell_trigger_positive
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) : 1 ≤ e := by
  obtain ⟨birth, _, _, hb, _⟩ :=
    collectionPrefixCell_anchor_origin rate rewards C_star C_h e b z hz
  by_contra h
  have he : e = 0 := by omega
  simp only [he, List.take_zero, List.not_mem_nil] at hb

/-- The same full original word, now obtained from literal prefix membership. -/
def collectionWord :
    List (RecordedQueueRun.RoundInput p.K) :=
  actualOriginalWord rate rewards C_star C_h z
    (collectionPrefixCell_launch rate rewards C_star C_h e b z hz)

/-- The actual local prefix is within this very word. -/
theorem collectionWord_bound :
    b ≤ (collectionWord rate rewards C_star C_h e b z hz).length := by
  rw [collectionWord, actualOriginalWord_length]
  exact hz.2.1

/-- Numerical state of the same actual original word at a literal index. -/
def collectionState (k : ℕ) : RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run (queueParameters rate)
    ((collectionWord rate rewards C_star C_h e b z hz).take k)

local notation "actualWord" => collectionWord rate rewards C_star C_h e b z hz
local notation "actualPayload" => oldPayload rate rewards C_star C_h e b z hz
local notation "stateAt" => collectionState rate rewards C_star C_h e b z hz

/-- The actual input of the proposal-triggering predecessor update. -/
def triggerInput : RecordedQueueRun.RoundInput p.K :=
  actualWord[e - 1]'(by
    have := collectionWord_bound rate rewards C_star C_h e b z hz
    have := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
    have := hz.1
    omega)

/-- Actual collection input at the specified relative window index. -/
def windowInput (i : Fin (b - e)) : RecordedQueueRun.RoundInput p.K :=
  actualWord[e + i.val]'(by
    have := collectionWord_bound rate rewards C_star C_h e b z hz
    have := hz.1
    omega)

/-- The literal prefix event with its inherited source Borel structure. -/
abbrev PrefixSource :=
  {z : SourceInput p //
    z ∈ collectionPrefixCell rate rewards C_star C_h e b}

local notation "CellSource" => PrefixSource rate rewards C_star C_h e b

/-- The triggering residual draw on the actual original numerical word. -/
def triggerSampler :=
  DeferredRefreshUniformKernels.sampleResidual p (queueParameters rate)
    (stateAt (e - 1)) (triggerInput rate rewards C_star C_h e b z hz)
    (actualPayload).anchor (actualPayload).anchor_pos

/-- A subsequent actual numerical update with its fresh proposal/residual pair. -/
def transitionSampler (i : Fin (b - e)) :=
  DeferredRefreshUniformKernels.sampleRecordedRefresh p (queueParameters rate)
    (stateAt (e + i.val)) (windowInput rate rewards C_star C_h e b z hz i)
    (actualPayload).anchor (actualPayload).anchor_pos

/-- Product law of one triggering scalar and the chronological fresh pairs. -/
def prefixUniformLaw (n : ℕ) : MeasureTheory.Measure (PrefixCoordinates n) :=
  ContinuousControlSlice.scalarLaw.prod
    (MeasureTheory.Measure.pi (fun _ : Fin n =>
      ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw))

/-- The sampled hidden set at a relative prefix, initialized by the actual
triggering residual and using the actual old anchor. -/
def sampledPrefix
    (n : ℕ) (hn : n ≤ b - e)
    (coordinates : PrefixCoordinates n) :
    CanonicalOrientedSetLaw.SlowSet p.K p.m :=
  DeferredRefreshUniformEvaluator.prefixValue p
    (queueParameters rate)
    (actualWord) e b
    (collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz)
    hz.1 (collectionWord_bound rate rewards C_star C_h e b z hz)
    (actualPayload).anchor
    (actualPayload).anchor_pos n hn coordinates

/-- Borelness on each actual physical-path-fixed section. -/
theorem measurable_sampledPrefix
    (n : ℕ) (hn : n ≤ b - e) :
    Measurable (sampledPrefix rate rewards C_star C_h e b z hz n hn) :=
  DeferredRefreshUniformEvaluator.measurable_prefixValue _ _ _ _ _ _ _ _ _ _ _

/-- The first draw uses the pre-trigger residual, rather than the post-trigger slow law. -/
theorem sampledPrefix_zero
    (coordinates : PrefixCoordinates 0) :
    sampledPrefix rate rewards C_star C_h e b z hz 0 (by omega) coordinates =
      triggerSampler rate rewards C_star C_h e b z hz coordinates.1 := rfl

/-- The full hidden path; coordinate `i` reads the trigger and first `i` pairs. -/
def sampledPath
    (n : ℕ) (hn : n ≤ b - e)
    (coordinates : PrefixCoordinates n) :
    Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m :=
  fun i => sampledPrefix rate rewards C_star C_h e b z hz i.val (by omega)
    (coordinates.1, fun j => coordinates.2 ⟨j.val, by omega⟩)

/-- Each coordinate of the finite path is Borel in the independent entries. -/
theorem measurable_sampledPath
    (n : ℕ) (hn : n ≤ b - e) :
    Measurable (sampledPath rate rewards C_star C_h e b z hz n hn) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_sampledPrefix rate rewards C_star C_h e b z hz i.val (by omega)).comp
    (measurable_fst.prodMk (measurable_pi_iff.mpr
      (fun j => (measurable_pi_apply _).comp measurable_snd)))

/-- The finite path starts with precisely the triggering residual sample. -/
theorem sampledPath_zero
    (n : ℕ) (hn : n ≤ b - e)
    (coordinates : PrefixCoordinates n) :
    sampledPath rate rewards C_star C_h e b z hz n hn coordinates 0 =
      triggerSampler rate rewards C_star C_h e b z hz coordinates.1 := rfl

/-- The next set uses the actual `e+i` input and the next fresh pair. -/
theorem sampledPath_succ
    (n : ℕ) (hn : n ≤ b - e)
    (coordinates : PrefixCoordinates n) (i : Fin n) :
    sampledPath rate rewards C_star C_h e b z hz n hn coordinates i.succ =
      transitionSampler rate rewards C_star C_h e b z hz ⟨i.val, by omega⟩
        (sampledPath rate rewards C_star C_h e b z hz n hn coordinates i.castSucc)
        (coordinates.2 i) := rfl

/-- A path cylinder is the rectangle in its trigger and dated transition pairs. -/
theorem sampledPath_cylinder
    (n : ℕ) (hn : n ≤ b - e)
    (V : Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    {coordinates | sampledPath rate rewards C_star C_h e b z hz n hn coordinates = V} =
      (triggerSampler rate rewards C_star C_h e b z hz ⁻¹' {V 0}) ×ˢ
      Set.pi Set.univ (fun i : Fin n =>
        transitionSampler rate rewards C_star C_h e b z hz ⟨i.val, by omega⟩ (V i.castSucc) ⁻¹'
            {V i.succ}) := by
  ext coordinates
  simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h
    constructor
    · rw [← sampledPath_zero rate rewards C_star C_h e b z hz n hn coordinates, h]
    · intro i
      rw [← h]
      exact (sampledPath_succ rate rewards C_star C_h e b z hz n hn coordinates i).symm
  · rintro ⟨hzero, hstep⟩
    funext i
    induction i using Fin.induction with
    | zero =>
        rw [sampledPath_zero]
        exact hzero
    | succ i ih =>
        rw [sampledPath_succ, ih]
        exact hstep i

/-- Literal residual-times-transition mass of one actual finite hidden path. -/
def pathAtom (n : ℕ) (hn : n ≤ b - e)
    (V : Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m) : ENNReal :=
  RecordedSlowRefresh.residualPMF p (queueParameters rate) (stateAt (e - 1))
    (triggerInput rate rewards C_star C_h e b z hz)
    (actualPayload).anchor (actualPayload).anchor_pos (V 0) *
  ∏ i : Fin n, RecordedSlowRefresh.recordedRefreshKernel p (queueParameters rate)
    (stateAt (e + i.val)) (windowInput rate rewards C_star C_h e b z hz ⟨i.val, by omega⟩)
    (actualPayload).anchor (actualPayload).anchor_pos rate.sourceCap (V i.castSucc) (V i.succ)

/-- Each path atom is its trigger residual times its chronological transition
atoms, including `n=0` and zero-mass paths. -/
theorem sampledPath_cylinder_measure
    (n : ℕ) (hn : n ≤ b - e)
    (V : Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    (prefixUniformLaw n)
      {coordinates | sampledPath rate rewards C_star C_h e b z hz n hn coordinates = V} =
      pathAtom rate rewards C_star C_h e b z hz n hn V := by
  unfold pathAtom
  rw [sampledPath_cylinder, prefixUniformLaw, MeasureTheory.Measure.prod_prod,
    MeasureTheory.Measure.pi_pi]
  simp only [triggerSampler, transitionSampler]
  congr 1
  · rw [DeferredRefreshUniformKernels.sampleResidual_atom, RecordedSlowRefresh.residualPMF_apply]
  · apply Finset.prod_congr rfl
    intro i _
    rw [← PMF.toMeasure_apply_singleton _ (V i.succ) (measurableSet_singleton _),
      ← DeferredRefreshUniformKernels.sampleRecordedRefresh_map p _ _ _ _ _ rate.sourceCap,
      MeasureTheory.Measure.map_apply
        (DeferredRefreshUniformKernels.measurable_sampleRecordedRefresh p _ _ _ _ _ _)
        (measurableSet_singleton _)]

/-- Clock preservation from the actual generated corrected launch. -/
private theorem actualRecord_clock
    (k : Fin (records).length) :
    let record := (records)[k.val]
    ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)
      record.input.time.val record.input.state := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      have hnil := (no_launch_complete_history rate z rewards C_star C_h hl).2.1
      have hk := k.isLt
      have hlen := congrArg List.length hnil
      simp only [List.length_nil] at hlen
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by rw [hl]; rfl)
      obtain ⟨first, hfirstLaunch, hfirst, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate z rewards C_star C_h hc
      have heq : first = active := Option.some.inj (hfirstLaunch.symm.trans hl)
      subst first
      have hrecords := completeSuffixRecords_on_launch rate z rewards C_star C_h active hl
      have hseed : ReferenceCoordinatorClockDomains.clockAt z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) (start) active := by
        simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclock := ReferenceRunClockPreservation.run_clockAt active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (start) (p.T - start)
        (by have := physicalStart_le_T rate z rewards C_star C_h; omega)
        (activeMode_of_launch_eq_some rate z rewards C_star C_h active hl) hseed
      exact (hclock.2.2.2 _ (by
        rw [← hrecords]
        exact List.getElem_mem k.isLt)).1

/-- Actual date bounds; the source's one-based dates are `s+e+1` and `s+b+1`. -/
theorem collectionPrefixCell_dates
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e b) :
    start < start + e ∧ start + e ≤ start + b ∧ start + b < p.T := by
  obtain ⟨he, r, q, base, hlive, _, hbefore, _⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e b z hz
  have hclock := actualRecord_clock rate rewards C_star C_h z ⟨e, he⟩
  simp only [ReferenceCoordinatorClockDomains.clockAt, hlive] at hclock
  have hg : r.gridBoundary ≤ p.T + 1 := by
    rw [hclock.2.2.2.2.1]
    have hvalid := hclock.2.1.2
    rw [hclock.2.2.1] at hvalid
    exact hvalid.2.1
  have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz
  have heb := hz.1
  omega

/-- The original zero-based cutoff date, determined from the source calendar. -/
def cutoffDate : Fin p.T :=
  ⟨start + e, by
    have h := collectionPrefixCell_dates rate rewards C_star C_h e b z hz
    omega⟩

/-- The current zero-based prefix date, including prefixes with no next call. -/
def prefixDate : Fin p.T :=
  ⟨start + b,
    (collectionPrefixCell_dates rate rewards C_star C_h e b z hz).2.2⟩

/-- Literal allocation: trigger label 1 at `s+e-1`, pair labels 0 and 1 at `s+e+i`. -/
def actualCoordinateIndex
    (n : ℕ) (hn : n ≤ b - e) :
    Unit ⊕ (Fin n ⊕ Fin n) → ReferenceFirstCollectionAuxiliarySeeds.Coordinate p :=
  fun i => (DeferredRefreshUniformEvaluator.coordinateIndex
    (start)
    (cutoffDate rate rewards C_star C_h e b z hz)
    (prefixDate rate rewards C_star C_h e b z hz)
    (collectionPrefixCell_dates rate rewards C_star C_h e b z hz).1 n
    (by simpa only [cutoffDate, prefixDate, Nat.add_sub_add_left] using hn) i).val

/-- Every consumed entry has a distinct calendar/label address. -/
theorem actualCoordinateIndex_injective
    (n : ℕ) (hn : n ≤ b - e) :
    Function.Injective (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn) := by
  exact Subtype.val_injective.comp
    (DeferredRefreshUniformEvaluator.coordinateIndex_injective _ _ _ _ _ _)

/-- The trigger coordinate has its exact absolute date and residual label. -/
theorem actualCoordinateIndex_trigger
    (n : ℕ) (hn : n ≤ b - e) :
    (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn (.inl ())).1.val = start + e - 1 ∧
      (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn (.inl ())).2 = 1 :=
  ⟨rfl, rfl⟩

/-- Each later pair uses its actual date and the two distinct labels. -/
theorem actualCoordinateIndex_step
    (n : ℕ) (hn : n ≤ b - e) (i : Fin n) :
    (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn (.inr (.inl i))).1.val =
        start + e + i.val ∧
      (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn (.inr (.inl i))).2 = 0 ∧
      (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn (.inr (.inr i))).1.val =
        start + e + i.val ∧
      (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn (.inr (.inr i))).2 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The injective allocation inherits independence from the existing Pi law. -/
theorem actualCoordinateIndex_independent
    (n : ℕ) (hn : n ≤ b - e) :
    ProbabilityTheory.iIndepFun (fun i => fun array : AuxiliaryArray p =>
        array (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn i))
      (auxiliaryUniformLaw p) := by
  exact (ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
      ContinuousControlSlice.scalarLaw)
    (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)).precomp
      (actualCoordinateIndex_injective rate rewards C_star C_h e b z hz n hn)

private theorem measurable_fin_pair {Ω : Type*} [MeasurableSpace Ω] {j k : ℕ}
    (f : Ω → Fin j × Fin k) (h : Measurable (fun x => ((f x).1.val, (f x).2.val))) :
    Measurable f := by
  apply measurable_to_countable'
  intro q
  convert measurableSet_eq_fun h (measurable_const (a := (q.1.val, q.2.val))) using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Prod.ext_iff, Fin.ext_iff]

/-- The actual cutoff and current prefix dates are jointly Borel. -/
theorem measurable_collectionDates :
    Measurable (fun x : CellSource => (cutoffDate rate rewards C_star C_h e b x.val x.property,
      prefixDate rate rewards C_star C_h e b x.val x.property)) := by
  apply measurable_fin_pair
  have hstart := (measurable_physicalStart rate rewards C_star C_h).comp
    (measurable_subtype_coe (p := fun z => z ∈ collectionPrefixCell rate rewards C_star C_h e b))
  exact (hstart.add_const e).prodMk (hstart.add_const b)

/-- Every used address is Borel in the original source's generated launch date. -/
theorem measurable_actualCoordinateIndex (n : ℕ) (hn : n ≤ b - e)
    (i : Unit ⊕ (Fin n ⊕ Fin n)) :
    Measurable (fun x : CellSource =>
      actualCoordinateIndex rate rewards C_star C_h e b x.val x.property n hn i) := by
  apply measurable_fin_pair
  have hstart := (measurable_physicalStart rate rewards C_star C_h).comp
    (measurable_subtype_coe (p := fun z => z ∈ collectionPrefixCell rate rewards C_star C_h e b))
  cases i with
  | inl u => exact ((hstart.add_const e).sub_const 1).prodMk measurable_const
  | inr j => cases j with
    | inl j => exact ((hstart.add_const e).add_const j.val).prodMk measurable_const
    | inr j => exact ((hstart.add_const e).add_const j.val).prodMk measurable_const

/-- Literal dated extraction from the whole array on the prefix cell. -/
def actualPrefixCoordinates (x : CellSource) (n : ℕ) (hn : n ≤ b - e)
    (array : AuxiliaryArray p) :
    PrefixCoordinates n :=
  (array (actualCoordinateIndex rate rewards C_star C_h e b x.val x.property n hn (.inl ())),
    fun i =>
      (array (actualCoordinateIndex rate rewards C_star C_h e b x.val x.property n hn (.inr (.inl i))),
        array (actualCoordinateIndex rate rewards C_star C_h e b x.val x.property n hn (.inr (.inr i)))))

/-- Joint Borelness of dated extraction in the whole original source and array. -/
theorem measurable_actualPrefixCoordinates_joint (n : ℕ) (hn : n ≤ b - e) :
    Measurable (fun w : CellSource × AuxiliaryArray p =>
      actualPrefixCoordinates rate rewards C_star C_h e b w.1 n hn w.2) := by
  have heval : Measurable (fun w : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p ×
      AuxiliaryArray p => w.2 w.1) :=
    measurable_from_prod_countable_right (fun i => measurable_pi_apply i)
  have hentry (i : Unit ⊕ (Fin n ⊕ Fin n)) := heval.comp
    (((measurable_actualCoordinateIndex rate rewards C_star C_h e b n hn i).comp
      measurable_fst).prodMk measurable_snd)
  exact (hentry (.inl ())).prodMk (measurable_pi_iff.mpr
    (fun i => (hentry (.inr (.inl i))).prodMk (hentry (.inr (.inr i)))))

/-- The path reads only its dated trigger and first `n` pairs from the whole array. -/
def sampledArrayPath
    (n : ℕ) (hn : n ≤ b - e)
    (array : AuxiliaryArray p) :
    Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m :=
  sampledPath rate rewards C_star C_h e b z hz n hn
    (actualPrefixCoordinates rate rewards C_star C_h e b ⟨z, hz⟩ n hn array)

/-- The fixed-source evaluator is Borel in the whole analytical array. -/
theorem measurable_sampledArrayPath
    (n : ℕ) (hn : n ≤ b - e) :
    Measurable (sampledArrayPath rate rewards C_star C_h e b z hz n hn) :=
  (measurable_sampledPath rate rewards C_star C_h e b z hz n hn).comp
    ((measurable_actualPrefixCoordinates_joint rate rewards C_star C_h e b n hn).comp
      ((measurable_const (a := (⟨z, hz⟩ : CellSource))).prodMk measurable_id))

/-- The extracted entries have their trigger-times-pairs product law. -/
theorem actualPrefixCoordinates_map
    (n : ℕ) (hn : n ≤ b - e) :
    (auxiliaryUniformLaw p).map (actualPrefixCoordinates rate rewards C_star C_h e b ⟨z, hz⟩ n hn) =
      prefixUniformLaw n := by
  exact ((DeferredRefreshUniformEvaluator.prefixCoordinates_measurePreserving
    (start)
    (cutoffDate rate rewards C_star C_h e b z hz)
    (prefixDate rate rewards C_star C_h e b z hz)
    (collectionPrefixCell_dates rate rewards C_star C_h e b z hz).1 n
    (by simpa only [cutoffDate, prefixDate, Nat.add_sub_add_left] using hn)).comp
    ⟨ReferenceFirstCollectionAuxiliarySeeds.measurable_auxiliaryBlock _ _,
      ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw_map_auxiliaryBlock _ _⟩).map_eq

/-- Every fixed-source path test has the explicit finite product law. -/
theorem sampledArrayPath_map
    (n : ℕ) (hn : n ≤ b - e) :
    (auxiliaryUniformLaw p).map (sampledArrayPath rate rewards C_star C_h e b z hz n hn) =
      (prefixUniformLaw n).map (sampledPath rate rewards C_star C_h e b z hz n hn) := by
  have hcoordinates := actualPrefixCoordinates_map rate rewards C_star C_h e b z hz n hn
  have hmeasurable :=
    (measurable_actualPrefixCoordinates_joint rate rewards C_star C_h e b n hn).comp
      ((measurable_const (a := (⟨z, hz⟩ : CellSource))).prodMk measurable_id)
  exact (MeasureTheory.Measure.map_map
    (measurable_sampledPath rate rewards C_star C_h e b z hz n hn)
    hmeasurable).symm.trans
      (congrArg (fun μ => μ.map (sampledPath rate rewards C_star C_h e b z hz n hn)) hcoordinates)

private theorem startRound_noCutoff_preserves_u
    (clock : CoordinatorPhaseClock.ClockRegisters p) (time : Fin p.T)
    (pending : Finset (Fin (p.m - 1))) (result : CoordinatorPhaseClock.StartRoundResult p)
    (hu : clock.u = none)
    (hd : CoordinatorPhaseClock.detectCutoff clock time = .ok .noCutoff)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending = .ok result) :
    result.clock.u = none := by
  classical
  unfold CoordinatorPhaseClock.startRound at hs
  split at hs <;> try contradiction
  split at hs <;> try contradiction
  split at hs <;> try contradiction
  rw [hd] at hs
  dsimp only at hs
  split at hs
  · split at hs <;> try contradiction
    cases hs
    rfl
  · cases hs
    exact hu

/-- The actual pre-boundary cutoff was caused by the correctly dated preceding
physical proposal; its bit and clock are derived from this source. -/
theorem collectionPrefixCell_trigger_proposal :
    ∃ stamp : Fin p.T, stamp.val + 1 = (cutoffDate rate rewards C_star C_h e b z hz).val ∧
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) stamp = true := by
  classical
  obtain ⟨he, r, q, base, hlive, hcut, hbefore, _⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e b z hz
  let record := (records)[e]'he
  have htime : record.input.time.val = start + e :=
    ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h e record (List.getElem?_eq_getElem he)
  have hclock := actualRecord_clock rate rewards C_star C_h z ⟨e, he⟩
  simp only [ReferenceCoordinatorClockDomains.clockAt, hlive] at hclock
  obtain ⟨hstamp, _hvalid, hsigma, hu, hg, _hpast, _hgridPast, htoken⟩ := hclock
  have hdate : r.time.val + 1 = (cutoffDate rate rewards C_star C_h e b z hz).val := by
    change r.time.val + 1 = start + e
    exact hstamp.trans htime
  refine ⟨r.time, hdate, ?_⟩
  by_contra hbit
  have hfalse : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) r.time = false := by
    cases hb : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) r.time <;> simp_all
  have hread := CoordinatorPhaseClock.savedPriorProposal_correct r.priorClock record.input.time
    r.time false (by simpa only [hfalse] using htoken) hstamp
  have hnotgrid : FollowerCutoffScan.calendarRound record.input.time ≠ r.priorClock.g := by
    change record.input.time.val + 1 ≠ r.priorClock.g
    have heb := hz.1
    omega
  have hdetect : CoordinatorPhaseClock.detectCutoff r.priorClock record.input.time =
      .ok .noCutoff := by
    simp only [CoordinatorPhaseClock.detectCutoff, hnotgrid, ite_false, hread]
    split <;> rfl
  have hdispatch : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .live r q base (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput record.input r q base)) := by
    change record.input.state.coordinator = .live r q base at hlive
    change ReferenceActivePhysicalStep.dispatch record.input = _
    simp only [ReferenceActivePhysicalStep.dispatch, hlive, CoordinatorRoundDispatch.dispatch]
    rfl
  change ReferenceCollectionPhaseHistory.cutoffChosen record.input = true at hcut
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  rw [hdispatch] at hcut
  cases ho : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput record.input r q base) with
  | cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hshape hpending hno selected =>
      have hpreserve := startRound_noCutoff_preserves_u rate r.priorClock record.input.time
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).clockPending
        dispatched.startResult hu hdetect hstart
      have hchanged := congrArg CoordinatorPhaseClock.ClockRegisters.u hshape
      change dispatched.startResult.clock.u = some record.input.time at hchanged
      rw [hpreserve] at hchanged
      cases hchanged
  | clockFailure failure h => simp only [ho] at hcut; cases hcut
  | initializerFailure dispatched hs checked hi => simp only [ho] at hcut; cases hcut
  | localFailure dispatched hs reason => simp only [ho] at hcut; cases hcut
  | continuingChosen dispatched hs continuation selected => simp only [ho] at hcut; cases hcut

/-- The cell's retained test is exactly this word's pre-round overflow flag. -/
theorem collectionWord_retained :
    (stateAt b).overflow = false := by
  have hcellData := hz
  obtain ⟨_, hbound, he, hcell⟩ := hcellData
  cases hc : (records)[e].input.state.coordinator with
  | live r q base =>
      rw [hc] at hcell
      obtain ⟨o, ho, hclear⟩ := hcell.2.2.2
      have hp := actualOriginalWord_prefix rate rewards C_star C_h z
        (collectionPrefixCell_launch rate rewards C_star C_h e b z hz) b hbound
      change prefixInputs rate rewards C_star C_h (start + b) z = some ((actualWord).take b) at hp
      unfold prefixReadout at ho
      rw [hp] at ho
      have heq := Option.some.inj ho
      exact (congrArg (fun readout => readout.2.1) heq).trans hclear
  | first => simp only [hc] at hcell
  | collection P ledger saved => simp only [hc] at hcell
  | dagger => simp only [hc] at hcell

/-- The sampled endpoint has the actual residual-initialized kernel iterate. -/
theorem sampledPrefix_map
    (n : ℕ) (hn : n ≤ b - e) :
    (prefixUniformLaw n).map (sampledPrefix rate rewards C_star C_h e b z hz n hn) =
      (DeferredRefreshWindow.windowPrefixPMF p (queueParameters rate) (actualWord) e b
        (collectionPrefixCell_trigger_positive rate rewards C_star C_h e b z hz) hz.1
        (collectionWord_bound rate rewards C_star C_h e b z hz) (actualPayload).anchor
        (actualPayload).anchor_pos rate.sourceCap n).toMeasure :=
  DeferredRefreshUniformEvaluator.prefixValue_map _ _ _ _ _ _ _ _ _ rate.sourceCap n hn

/-- The last coordinate of the full path is the same endpoint evaluator. -/
theorem sampledPath_last
    (n : ℕ) (hn : n ≤ b - e)
    (coordinates : PrefixCoordinates n) :
    sampledPath rate rewards C_star C_h e b z hz n hn coordinates (Fin.last n) =
      sampledPrefix rate rewards C_star C_h e b z hz n hn coordinates := rfl

/-- The evaluator factors through its used entries in the retained whole array. -/
theorem sampledArrayPath_eq_of_used_entries
    (n : ℕ) (hn : n ≤ b - e)
    (array other : AuxiliaryArray p)
    (h : ∀ i, array (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn i) =
      other (actualCoordinateIndex rate rewards C_star C_h e b z hz n hn i)) :
    sampledArrayPath rate rewards C_star C_h e b z hz n hn array =
      sampledArrayPath rate rewards C_star C_h e b z hz n hn other := by
  unfold sampledArrayPath
  congr 1
  apply Prod.ext
  · exact h (.inl ())
  · funext i
    exact Prod.ext (h (.inr (.inl i))) (h (.inr (.inr i)))

private theorem split_last_pair (n : ℕ) :
    MeasureTheory.MeasurePreserving (fun coordinates : PrefixCoordinates (n + 1) =>
        ((coordinates.1, fun i : Fin n => coordinates.2 i.castSucc), coordinates.2 (Fin.last n)))
      (prefixUniformLaw (n + 1)) ((prefixUniformLaw n).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) := by
  unfold prefixUniformLaw
  let ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw
  have hhead := MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ν) (Fin.last n)
  have htail := (MeasureTheory.Measure.measurePreserving_swap
    (μ := ν) (ν := MeasureTheory.Measure.pi (fun _ : Fin n => ν))).comp hhead
  have hpair := (MeasureTheory.MeasurePreserving.id ContinuousControlSlice.scalarLaw).prod htail
  have hassoc := (MeasureTheory.measurePreserving_prodAssoc ContinuousControlSlice.scalarLaw
    (MeasureTheory.Measure.pi (fun _ : Fin n => ν)) ν).symm
  convert hassoc.comp hpair using 1
  change (fun coordinates : PrefixCoordinates (n + 1) =>
      ((coordinates.1, fun i : Fin n => coordinates.2 i.castSucc), coordinates.2 (Fin.last n))) =
    (fun coordinates =>
      ((coordinates.1, fun i => coordinates.2 ((Fin.last n).succAbove i)),
        coordinates.2 (Fin.last n)))
  simp only [Fin.succAbove_last]

/-- The entire sampled past and next unused proposal/residual pair have their
product law on each fixed physical section. -/
theorem sampledPath_freshPair_map
    (n : ℕ) (hn : n < b - e) :
    (prefixUniformLaw (n + 1)).map (fun coordinates : PrefixCoordinates (n + 1) =>
        (sampledPath rate rewards C_star C_h e b z hz n hn.le
          (coordinates.1, fun i => coordinates.2 i.castSucc), coordinates.2 (Fin.last n))) =
      ((prefixUniformLaw n).map (sampledPath rate rewards C_star C_h e b z hz n hn.le)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  have hsplit := split_last_pair n
  have hpast := measurable_sampledPath rate rewards C_star C_h e b z hz n hn.le
  have h := congrArg (fun μ => μ.map (Prod.map
    (sampledPath rate rewards C_star C_h e b z hz n hn.le) id)) hsplit.map_eq
  rw [MeasureTheory.Measure.map_map (hpast.prodMap measurable_id) hsplit.measurable,
    ← MeasureTheory.Measure.map_prod_map _ _ hpast measurable_id,
    MeasureTheory.Measure.map_id] at h
  exact h

/-- The next pair uses labels 0 and 1 at date `s+e+n`. -/
def freshArrayPair
    (n : ℕ) (hn : n < b - e)
    (array : AuxiliaryArray p) :
    ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar :=
  (array (actualCoordinateIndex rate rewards C_star C_h e b z hz (n + 1)
      (by omega) (.inr (.inl (Fin.last n)))),
    array (actualCoordinateIndex rate rewards C_star C_h e b z hz (n + 1)
      (by omega) (.inr (.inr (Fin.last n)))))

/-- Product law of the sampled past and next pair in the whole array. -/
theorem sampledArrayPath_freshPair_map
    (n : ℕ) (hn : n < b - e) :
    (auxiliaryUniformLaw p).map
      (fun array => (sampledArrayPath rate rewards C_star C_h e b z hz n hn.le array,
        freshArrayPair rate rewards C_star C_h e b z hz n hn array)) = ((prefixUniformLaw n).map
        (sampledPath rate rewards C_star C_h e b z hz n hn.le)).prod
          (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) := by
  have hcoordinates := actualPrefixCoordinates_map rate rewards C_star C_h e b z hz
    (n + 1) (by omega)
  have hsplit := split_last_pair n
  have hpast := measurable_sampledPath rate rewards C_star C_h e b z hz n hn.le
  have hlocal := (hpast.prodMap measurable_id).comp hsplit.measurable
  have hselect :=
    (measurable_actualPrefixCoordinates_joint rate rewards C_star C_h e b (n + 1)
      (by omega)).comp ((measurable_const (a := (⟨z, hz⟩ : CellSource))).prodMk measurable_id)
  have hmap := (MeasureTheory.Measure.map_map
    (μ := auxiliaryUniformLaw p) hlocal hselect).symm
  exact hmap.trans ((congrArg (fun μ => μ.map
    ((Prod.map (sampledPath rate rewards C_star C_h e b z hz n hn.le) id) ∘
      (fun coordinates : PrefixCoordinates (n + 1) =>
        ((coordinates.1, fun i : Fin n => coordinates.2 i.castSucc),
          coordinates.2 (Fin.last n))))) hcoordinates).trans
    (sampledPath_freshPair_map rate rewards C_star C_h e b z hz n hn))

/-- The next proposal and refresh scalars are fresh jointly with every Borel
test of the entire sampled past. -/
theorem sampledArrayPath_freshPair_test
    (n : ℕ) (hn : n < b - e)
    (B : Set (Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m))
    (hB : MeasurableSet B)
    (C D : Set ContinuousControlSlice.Scalar) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    (auxiliaryUniformLaw p)
      {array | sampledArrayPath rate rewards C_star C_h e b z hz n hn.le array ∈ B ∧
        (freshArrayPair rate rewards C_star C_h e b z hz n hn array).1 ∈ C ∧
        (freshArrayPair rate rewards C_star C_h e b z hz n hn array).2 ∈ D} =
      ((prefixUniformLaw n).map (sampledPath rate rewards C_star C_h e b z hz n hn.le)) B *
          (ContinuousControlSlice.scalarLaw C * ContinuousControlSlice.scalarLaw D) := by
  have hpair : Measurable (freshArrayPair rate rewards C_star C_h e b z hz n hn) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hmap := congrArg (fun μ => μ (B ×ˢ (C ×ˢ D)))
    (sampledArrayPath_freshPair_map rate rewards C_star C_h e b z hz n hn)
  rw [MeasureTheory.Measure.map_apply
      ((measurable_sampledArrayPath rate rewards C_star C_h e b z hz n hn.le).prodMk hpair)
      (hB.prod (hC.prod hD)), MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.prod_prod] at hmap
  exact hmap

private theorem threshold_event_eq (probability : ℝ) :
    {alpha : ContinuousControlSlice.Scalar |
      FollowerCutoffScan.thresholdProposalBit alpha probability = true} =
      (Subtype.val : ContinuousControlSlice.Scalar → ℝ) ⁻¹' Set.Iio probability := by
  ext alpha
  simp only [FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq,
    Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]

private theorem threshold_coin_measure (probability : ℝ) (hle : probability ≤ 1) :
    ContinuousControlSlice.scalarLaw {alpha : ContinuousControlSlice.Scalar |
        FollowerCutoffScan.thresholdProposalBit alpha probability = true} =
      ENNReal.ofReal probability := by
  change ContinuousCategorical.uniform _ = _
  rw [threshold_event_eq, ContinuousCategorical.uniform_preimage_val,
    Set.inter_comm, Set.Ico_inter_Iio, min_eq_right hle, Real.volume_Ico, sub_zero]

/-- The next gated coin and residual draw have their actual joint mass,
independently of each Borel past-path test on the fixed physical section. -/
theorem sampledArrayPath_fresh_refresh_test
    (n : ℕ) (hn : n < b - e)
    (B : Set (Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m))
    (hB : MeasurableSet B) (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    let Q := queueParameters rate
    let L := actualWord
    let P := actualPayload
    let state := RecordedQueueRun.run Q (L.take (e + n))
    let round := windowInput rate rewards C_star C_h e b z hz ⟨n, hn⟩
    (auxiliaryUniformLaw p)
      {array | sampledArrayPath rate rewards C_star C_h e b z hz n hn.le array ∈ B ∧
        FollowerCutoffScan.thresholdProposalBit
          (freshArrayPair rate rewards C_star C_h e b z hz n hn array).1
          (RecordedSlowRefresh.proposalProbability p Q state round) = true ∧
        DeferredRefreshUniformKernels.sampleResidual p Q state round P.anchor P.anchor_pos
          (freshArrayPair rate rewards C_star C_h e b z hz n hn array).2 = U} =
      ((prefixUniformLaw n).map (sampledPath rate rewards C_star C_h e b z hz n hn.le)) B *
      (ENNReal.ofReal (RecordedSlowRefresh.proposalProbability p Q state round) *
        RecordedSlowRefresh.residualPMF p Q state round P.anchor P.anchor_pos U) := by
  intro Q L P state round
  have h := sampledArrayPath_freshPair_test rate rewards C_star C_h e b z hz n hn B hB
    {alpha | FollowerCutoffScan.thresholdProposalBit alpha
      (RecordedSlowRefresh.proposalProbability p Q state round) = true}
    (DeferredRefreshUniformKernels.sampleResidual p Q state round P.anchor P.anchor_pos ⁻¹' {U})
    (by rw [threshold_event_eq]; exact measurableSet_Iio.preimage measurable_subtype_coe)
    ((DeferredRefreshUniformKernels.measurable_sampleResidual p Q state round P.anchor P.anchor_pos)
      (measurableSet_singleton U))
  rw [threshold_coin_measure _
      (RecordedSlowRefresh.proposalProbability_le_one p Q state round rate.sourceCap),
    DeferredRefreshUniformKernels.sampleResidual_atom] at h
  simpa only [RecordedSlowRefresh.residualPMF_apply, Set.mem_ofPred_eq,
    Set.mem_preimage, Set.mem_singleton_iff] using h

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) := LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurable_cutoffOnLive :
    Measurable (fun x : LiveInput p rate =>
      ReferenceCollectionPhaseHistory.cutoffChosen x.val) := by
  let tag : ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
    | .cutoffChosen _ _ _ => true
    | _ => false
  have h := (measurable_of_countable tag).comp
    (ReferenceLiveDispatchOutputMeasurability.measurable_dispatchLive_outcomeData.comp
      (measurable_liveCoordinates (p := p) (rate := rate)))
  convert h using 1
  funext x
  dsimp only [Function.comp_def, liveCoordinates]
  rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput]
  unfold ReferenceCollectionPhaseHistory.cutoffChosen ReferenceActivePhysicalStep.prepare
  dsimp only
  rw [ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
    x.val _ _ _ (live_state x)]
  cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x.val
    (liveRegisters x)
    (liveOwned x)
    (liveBase x)) <;> rfl

local instance : MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) :=
  ReferenceCollectionOutcomeMeasurability.instMeasurableSpaceClockObservation

private theorem measurable_laterChosen :
    Measurable (ReferenceCollectionPhaseHistory.laterChosen (p := p) (rate := rate)) := by
  classical
  let tag : Unit ⊕ FullObservation p rate → Bool :=
    Sum.elim (fun _ => false) (fun o => decide (o.2.2.1 = .laterChosen))
  have ht : Measurable tag := measurable_const.sumElim
    ((measurable_of_countable (fun t : ReferenceCollectionOutcomeMeasurability.CollectionTag p =>
      decide (t = .laterChosen))).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have h := (measurable_optionalElim false tag ht).comp
    (measurable_canonicalCollectionFullObservation (p := p) (rate := rate))
  convert h using 1
  funext input
  change ReferenceCollectionPhaseHistory.laterChosen input =
    optionalElim false tag (canonicalCollectionFullObservation input)
  cases hstate : input.state.coordinator
  case collection payload ledger proposal =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let bd : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
        ((payload, input.row), ledger, proposal, input.state.upDecoderBank, input.time)
      let z := ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨bd, hc⟩
      have hfull : canonicalCollectionFullObservation input =
          some (.inr (collectionFullObservation z)) := by
        rw [canonicalCollectionFullObservation_collection input payload ledger proposal hstate]
        unfold ReferenceCollectionOutcomeMeasurability.boundaryFullObservation
        rw [dite_eq_left (show ReferenceCollectionDispatchMeasurability.cutoffValid bd from hc)]
      have htag := collectionTag_eq_actual z
      unfold ReferenceCollectionPhaseHistory.laterChosen ReferenceActivePhysicalStep.prepare
      dsimp only
      rw [ReferenceCollectionDispatchMeasurability.dispatch_collection
        input payload ledger proposal hstate hc]
      cases hout : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceCollectionDispatchMeasurability.assemble z) <;>
        simp [hfull, tag, z, htag, hout, optionalElim, collectionFullObservation, outcomeTag]
    · have hobs := canonicalCollectionFullObservation_invalid
        input payload ledger proposal hstate hc
      simp only [hobs.1, optionalElim, tag, Sum.elim_inl]
      simp only [ReferenceCollectionPhaseHistory.laterChosen, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hstate, hc, dite_false]
  all_goals
    have hphase : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator input.state.coordinator) = none := by
      rw [hstate]
      rfl
    have hobs := canonicalCollectionFullObservation_absent input hphase
    simp only [hobs.1, optionalElim]
    simp only [ReferenceCollectionPhaseHistory.laterChosen, ReferenceActivePhysicalStep.prepare,
      ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
  all_goals rfl

/-- An actual successful later installation at a fixed original suffix index.
Missing physical records remain absent rather than receiving a stored value. -/
def laterInstallationAt (k : ℕ) : Set (SourceInput p) :=
  Subtype.val '' {x : IndexedSource
    rate rewards C_star C_h k | ReferenceCollectionPhaseHistory.laterChosen (actualRoundInputAt
        rate rewards C_star C_h k x) = true}

/-- The actual installation event is Borel through the original dispatch tag. -/
theorem measurableSet_laterInstallationAt (k : ℕ) :
    MeasurableSet (laterInstallationAt rate rewards C_star C_h k) :=
  (measurableSet_indexDomain
    rate rewards C_star C_h k).subtype_image
      ((measurableSet_singleton true).preimage ((measurable_laterChosen rate).comp
        (measurable_actualRoundInputAt rate rewards C_star C_h k)))

private theorem noInstallation_iff (z : SourceInput p) :
    (∀ k : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
      e < k.val → k.val < b → ReferenceCollectionPhaseHistory.laterChosen
        (completeSuffixRecords rate z rewards C_star C_h)[k.val].input = false) ↔
      ∀ k : ℕ, e < k → k < b → z ∉ laterInstallationAt rate rewards C_star C_h k := by
  constructor
  · intro h k hek hkb ⟨x, hx, hxz⟩
    subst z
    have hf := h ⟨k, x.property⟩ hek hkb
    change ReferenceCollectionPhaseHistory.laterChosen
      (completeSuffixRecords rate x.val rewards C_star C_h)[k].input = true at hx
    rw [hf] at hx
    cases hx
  · intro h k hek hkb
    cases hc : ReferenceCollectionPhaseHistory.laterChosen
        (completeSuffixRecords rate z rewards C_star C_h)[k.val].input with
    | false => rfl
    | true => exact False.elim (h k.val hek hkb ⟨⟨z, k.isLt⟩, hc, rfl⟩)

private theorem measurable_originalPrefixReadout (k : ℕ) :
    Measurable (fun z : SourceInput p =>
      prefixReadout rate rewards C_star C_h (physicalStart rate z rewards C_star C_h + k) z) := by
  have hread : Measurable (fun v : ℕ × SourceInput p =>
      prefixReadout rate rewards C_star C_h v.1 v.2) := by
    apply measurable_from_prod_countable_right
    intro n
    exact (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n).mono le_rfl le_top
  exact hread.comp (((measurable_physicalStart
    rate rewards C_star C_h).add_const k).prodMk measurable_id)

private theorem measurableSet_originalRetained :
    MeasurableSet {z : SourceInput p | ∃ o, prefixReadout rate rewards C_star C_h
        (physicalStart rate z rewards C_star C_h + b) z = some o ∧ o.2.1 = false} := by
  have hkeep := (measurable_optionalElim false
    (fun o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K => !o.2.1)
    ((measurable_of_countable Bool.not).comp (measurable_fst.comp measurable_snd))).comp
      (measurable_originalPrefixReadout rate rewards C_star C_h b)
  have hset := (measurableSet_singleton true).preimage hkeep
  convert hset using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_def]
  cases hr : prefixReadout rate rewards C_star C_h
      (physicalStart rate z rewards C_star C_h + b) z with
  | none => simp [optionalElim]
  | some o => simp [optionalElim]

/-- The literal arbitrary collection-prefix cell is Borel in the whole source. -/
theorem measurableSet_collectionPrefixCell :
    MeasurableSet (collectionPrefixCell rate rewards C_star C_h e b) := by
  let I := IndexedSource rate rewards C_star C_h e
  let input : I → ReferenceActivePhysicalStep.RoundInput p rate :=
    actualRoundInputAt rate rewards C_star C_h e
  have hi : Measurable input :=
    measurable_actualRoundInputAt rate rewards C_star C_h e
  let V : Set I := input ⁻¹' liveSet
  have hV : MeasurableSet V :=
    measurableSet_liveSet.preimage hi
  let live : V → LiveInput p rate :=
    fun x => ⟨input x.val, x.property⟩
  have hl : Measurable live := (hi.comp measurable_subtype_coe).subtype_mk
  let source : V → SourceInput p := fun x => x.val.val
  have hs : Measurable source := measurable_subtype_coe.comp measurable_subtype_coe
  have hstart := (measurable_physicalStart
    rate rewards C_star C_h).comp hs
  have hlen : Measurable (fun x : V =>
      (completeSuffixRecords rate (source x) rewards C_star C_h).length) := by
    simpa only [completeSuffixRecords_length, Function.comp_def] using
      (measurable_of_countable (fun s : ℕ => p.T - s)).comp hstart
  have hg := ((measurable_of_countable
    (fun c : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => c.gridBoundary)).comp
      measurable_liveCode).comp hl
  have hcut := (measurable_cutoffOnLive rate).comp hl
  have hno : MeasurableSet {z : SourceInput p |
      ∀ k : ℕ, e < k → k < b → z ∉ laterInstallationAt rate rewards C_star C_h k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => (measurableSet_laterInstallationAt
        rate rewards C_star C_h k).compl)))
  have hcondition := (MeasurableSet.const (e ≤ b)).inter
    ((measurableSet_le (measurable_const (a := b)) hlen).inter
      (((measurableSet_singleton true).preimage hcut).inter
        ((measurableSet_lt ((hstart.add_const b).add_const 1) hg).inter ((hno.preimage hs).inter
            ((measurableSet_originalRetained rate rewards C_star C_h b).preimage hs)))))
  have hevent : MeasurableSet {x : V | source x ∈ collectionPrefixCell rate rewards C_star C_h e b} := by
    convert hcondition using 1
    ext x
    have hc := live_state (live x)
    change ((completeSuffixRecords rate (source x) rewards C_star C_h)[e]'x.val.property).input.state.coordinator =
      .live _ _ _ at hc
    change (e ≤ b ∧ b ≤ (completeSuffixRecords rate (source x) rewards C_star C_h).length ∧
      ∃ he, _) ↔ _
    constructor
    · rintro ⟨heb, hb, he, hrest⟩
      rw [hc] at hrest
      exact ⟨heb, hb, hrest.1, hrest.2.1,
        (noInstallation_iff rate rewards C_star C_h e b (source x)).mp hrest.2.2.1, hrest.2.2.2⟩
    · rintro ⟨heb, hb, hcut, hbefore, hno, hretained⟩
      refine ⟨heb, hb, x.val.property, ?_⟩
      rw [hc]
      exact ⟨hcut, hbefore,
        (noInstallation_iff rate rewards C_star C_h e b (source x)).mpr hno, hretained⟩
  have himage := (measurableSet_indexDomain
    rate rewards C_star C_h e).subtype_image (hV.subtype_image hevent)
  convert himage using 1
  ext z
  constructor
  · intro hz
    obtain ⟨he, r, q, base, hc, _⟩ := collectionPrefixCell_live rate rewards C_star C_h e b z hz
    have hv : (⟨z, he⟩ : I) ∈ V := by
      change ∃ v, ReferenceActivePhysicalStepMeasurability.encodeCoordinator
        (completeSuffixRecords rate z rewards C_star C_h)[e].input.state.coordinator = Sum.inr (Sum.inl v)
      exact ⟨(r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r q base), by rw [hc]; rfl⟩
    exact ⟨⟨z, he⟩, ⟨⟨⟨z, he⟩, hv⟩, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hx

private theorem measurable_of_some {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] (f : Ω → α)
    (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have hencode : Measurable (Equiv.optionEquivSumPUnit α) := comap_measurable _
  have hsum : Measurable (fun x => (Sum.inl (f x) : α ⊕ PUnit)) := hencode.comp hf
  have hinl : MeasurableEmbedding (@Sum.inl α PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp hsum

/-- The full old anchor, read from the actual incoming LIVE payload, is Borel. -/
theorem measurable_oldAnchor :
    Measurable (fun x : PrefixSource rate rewards C_star C_h e b =>
      (oldPayload rate rewards C_star C_h e b x.val x.property).anchor) := by
  let indexed : PrefixSource rate rewards C_star C_h e b →
      IndexedSource rate rewards C_star C_h e :=
    fun x => ⟨x.val, x.property.2.2.choose⟩
  have hi : Measurable indexed := measurable_subtype_coe.subtype_mk
  let input := fun x : PrefixSource rate rewards C_star C_h e b =>
    actualRoundInputAt rate rewards C_star C_h e (indexed x)
  have hinput : Measurable input :=
    (measurable_actualRoundInputAt rate rewards C_star C_h e).comp hi
  have hLive (x : PrefixSource rate rewards C_star C_h e b) :
      input x ∈ liveSet := by
    obtain ⟨he, r, q, base, hlive, _⟩ :=
      collectionPrefixCell_live rate rewards C_star C_h e b x.val x.property
    change ∃ v, ReferenceActivePhysicalStepMeasurability.encodeCoordinator
      (input x).state.coordinator = Sum.inr (Sum.inl v)
    refine ⟨(r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r q base), ?_⟩
    change (completeSuffixRecords rate x.val rewards C_star C_h)[e].input.state.coordinator =
      .live r q base at hlive
    change ReferenceActivePhysicalStepMeasurability.encodeCoordinator
      (completeSuffixRecords rate x.val rewards C_star C_h)[e].input.state.coordinator = _
    rw [hlive]
    rfl
  let live := fun x : PrefixSource rate rewards C_star C_h e b =>
    (⟨input x, hLive x⟩ : LiveInput p rate)
  have hl : Measurable live := hinput.subtype_mk
  have hanchor := AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_livePayload.comp hl)
  convert hanchor using 1
  funext x
  obtain ⟨he, r, q, base, hlive, _, _, hp⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e b x.val x.property
  rw [oldPayload_eq rate rewards C_star C_h e b x.val x.property r.payload hp]
  have hstate := live_state (live x)
  change ((completeSuffixRecords rate x.val rewards C_star C_h)[e]'he).input.state.coordinator =
    .live _ _ _ at hstate
  have hr := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
    (hlive.symm.trans hstate)).1
  exact congrArg (fun r => r.payload.anchor) hr

/-- Every state through `b` has its original optional numerical readout. -/
theorem collectionWord_readout
    (k : ℕ) (hk : k ≤ b) :
    prefixReadout rate rewards C_star C_h (physicalStart rate z rewards C_star C_h + k) z =
      some (stateReadout (stateAt k)) := by
  unfold prefixReadout
  rw [actualOriginalWord_prefix rate rewards C_star C_h z
    (collectionPrefixCell_launch rate rewards C_star C_h e b z hz) k (hk.trans hz.2.1)]
  rfl

/-- The actual numerical state readout is Borel at its source-dependent date. -/
theorem measurable_collectionWord_stateReadout
    (k : ℕ) (hk : k ≤ b) :
    Measurable (fun x : PrefixSource rate rewards C_star C_h e b =>
      stateReadout (RecordedQueueRun.run (queueParameters rate)
          ((collectionWord rate rewards C_star C_h e b x.val x.property).take k))) := by
  apply measurable_of_some
  have h := (measurable_originalPrefixReadout rate rewards C_star C_h k).comp
    (measurable_subtype_coe (p := fun z => z ∈ collectionPrefixCell rate rewards C_star C_h e b))
  convert h using 1
  funext x
  exact (collectionWord_readout rate rewards C_star C_h e b x.val x.property k hk).symm

local notation "Q" => queueParameters rate
local notation "L" => fun x : CellSource => collectionWord rate rewards C_star C_h e b (Subtype.val x) (Subtype.property x)
local notation "P" => fun x : CellSource => oldPayload rate rewards C_star C_h e b (Subtype.val x) (Subtype.property x)
local notation "S" => fun (x : CellSource) (k : ℕ) => RecordedQueueRun.run Q (List.take k (L x))

/-- Current slow masses are Borel in the actual source and its derived old anchor. -/
theorem measurable_collectionSlowMass (k : ℕ) (hk : k ≤ b)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    Measurable (fun x : CellSource => RecordedSlowRefresh.recordedSlowMass p Q
      (S x k) (P x).anchor (P x).anchor_pos U) := by
  have hregisters := measurable_fst.comp
    (measurable_collectionWord_stateReadout rate rewards C_star C_h e b k hk)
  have hweights : Measurable (fun x : CellSource => RecordedQueueRun.scoreWeight Q (S x k)) := by
    exact (measurable_of_countable (fun r : Fin p.K → ℕ × ℕ =>
      fun a => ScoreWeights.scoreWeight (1 + 1 / ((Q).D : ℝ)) (r a).1)).comp hregisters
  have hanchor := measurable_oldAnchor rate rewards C_star C_h e b
  change Measurable (fun x : CellSource => CanonicalOrientedSetLaw.slowMarginal
    (RecordedQueueRun.scoreWeight Q (S x k)) (P x).anchor p.two_le_m p.m_lt_K
    (fun a => RecordedSlowRefresh.scoreWeight_pos Q (S x k) a) (P x).anchor_pos U)
  fun_prop [CanonicalOrientedSetLaw.slowMarginal,
    FiniteOrientationDisintegration.slowMarginal,
    FiniteOrientationDisintegration.orientedJointMass,
    FiniteOrientationDisintegration.orientationProbability,
    FiniteOrientationDisintegration.partitionFunction]

/-- Actual residual masses are Borel in the original source. -/
theorem measurable_collectionResidualMass (k : ℕ) (hk : k < b)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    Measurable (fun x : CellSource => RecordedSlowRefresh.residualMass p Q (S x k) ((L x)[k]'(by
        exact hk.trans_le (collectionWord_bound rate rewards C_star C_h e b x.val x.property)))
      (P x).anchor (P x).anchor_pos U) := by
  have hnow := measurable_collectionSlowMass rate rewards C_star C_h e b k hk.le U
  have hnext := measurable_collectionSlowMass rate rewards C_star C_h e b (k + 1) (by omega) U
  have h := (hnext.sub ((measurable_const (a := 1 - RecordedSlowRefresh.hazard p Q)).mul hnow)).div_const
    (RecordedSlowRefresh.hazard p Q)
  convert h using 1
  funext x
  unfold RecordedSlowRefresh.residualMass
  rw [← DeferredRefreshUniformEvaluator.numericalPrefix_succ Q (L x) k (by
    exact hk.trans_le (collectionWord_bound rate rewards C_star C_h e b x.val x.property))]
  rfl

/-- Each actual residual sample is jointly Borel in the source and fresh scalar. -/
theorem measurable_collectionResidualSample (k : ℕ) (hk : k < b) :
    Measurable (fun w : CellSource × ContinuousControlSlice.Scalar =>
      DeferredRefreshUniformKernels.sampleResidual p Q (S w.1 k) ((L w.1)[k]'(by
          exact hk.trans_le (collectionWord_bound rate rewards C_star C_h e b w.1.val w.1.property)))
      (P w.1).anchor (P w.1).anchor_pos w.2) := by
  apply measurable_to_countable'
  intro U
  let masses := fun (x : CellSource) (i : Fin (DeferredRefreshUniformKernels.residualEnumerationSize p)) =>
    DeferredRefreshUniformKernels.residualEnumMass p Q (S x k) ((L x)[k]'(by
        exact hk.trans_le (collectionWord_bound rate rewards C_star C_h e b x.val x.property)))
      (P x).anchor (P x).anchor_pos i
  have hmass (i : Fin (DeferredRefreshUniformKernels.residualEnumerationSize p)) :
      Measurable (fun x : CellSource => masses x i) :=
    measurable_collectionResidualMass rate rewards C_star C_h e b k hk
      (DeferredRefreshUniformKernels.residualOrder p i)
  have hlo : Measurable (fun x : CellSource => ContinuousCategorical.lower (masses x)
      ((DeferredRefreshUniformKernels.residualOrder p).symm U)) := by
    unfold ContinuousCategorical.lower
    exact Finset.measurable_sum _ (fun i _ => hmass i)
  have hup : Measurable (fun x : CellSource => ContinuousCategorical.upper (masses x)
      ((DeferredRefreshUniformKernels.residualOrder p).symm U)) := by
    unfold ContinuousCategorical.upper
    exact Finset.measurable_sum _ (fun i _ => hmass i)
  have hscalar : Measurable (fun w : CellSource × ContinuousControlSlice.Scalar => w.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  convert (measurableSet_le (hlo.comp measurable_fst) hscalar).inter
    (measurableSet_lt hscalar (hup.comp measurable_fst)) using 1
  ext w
  exact DeferredRefreshUniformKernels.sampleResidual_eq_iff p Q _ _ _ _ w.2 U

/-- The actual proposal gate is Borel through accepted history, including
enabled zero service and the first overflow update. -/
theorem measurable_collectionProposal (k : ℕ) (hk : k < b) :
    Measurable (fun x : CellSource => RecordedSlowRefresh.proposalProbability p Q
      (S x k) ((L x)[k]'(hk.trans_le
        (collectionWord_bound rate rewards C_star C_h e b x.val x.property)))) := by
  let a : Fin p.K := ⟨0, lt_trans (lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m) p.m_lt_K⟩
  have hhistory := (measurable_pi_apply a).comp (measurable_snd.comp (measurable_snd.comp
    (measurable_collectionWord_stateReadout rate rewards C_star C_h e b (k + 1) (by omega))))
  have hentry := (measurable_pi_apply k).comp (measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hhistory))
  have hflag := ((measurable_const (a := false)).sumElim
    (measurable_fst : Measurable (Prod.fst : Bool × ℕ → Bool))).comp hentry
  have h := (measurable_of_countable (fun flag : Bool =>
    if flag then RecordedSlowRefresh.hazard p Q else 0)).comp hflag
  convert h using 1
  funext x
  have hlen : ((S x k).records a).length = k := by
    have hl := hk.trans_le (collectionWord_bound rate rewards C_star C_h e b x.val x.property)
    simpa only [RecordedQueueRun.run, RecordedQueueRun.initialState, List.length_nil,
      zero_add, List.length_take, Nat.min_eq_left hl.le] using
      (RecordedEpisodeStability.execute_records_length Q ((L x).take k)
        (RecordedQueueRun.initialState p.K) a)
  have hkl := hk.trans_le (collectionWord_bound rate rewards C_star C_h e b x.val x.property)
  change RecordedSlowRefresh.proposalProbability p Q (S x k) ((L x)[k]'hkl) =
    if Sum.elim (fun _ : Unit => false) Prod.fst
      (ReferenceActiveHorizonMeasurability.listObservationAt ((S x (k + 1)).records a) k)
      then RecordedSlowRefresh.hazard p Q else 0
  dsimp only
  simp only [DeferredRefreshUniformEvaluator.numericalPrefix_succ Q (L x) k
    (hk.trans_le (collectionWord_bound rate rewards C_star C_h e b x.val x.property))]
  simp only [RecordedQueueRun.step, ReferenceActiveHorizonMeasurability.listObservationAt,
    List.getElem?_append, hlen, Nat.lt_irrefl, ite_false, Nat.sub_self,
    List.getElem?_cons_zero]
  cases ho : (S x k).overflow <;> cases he : ((L x)[k]'hkl).enabled <;>
    simp only [RecordedSlowRefresh.proposalProbability, ho, he, RecordedQueueRun.acceptedRecord,
      Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, ite_true, ite_false]
  all_goals rfl

/-- Each sampled prefix is Borel jointly in the original source and its scalars. -/
theorem measurable_sampledPrefix_joint (n : ℕ) (hn : n ≤ b - e) :
    Measurable (fun w : CellSource × PrefixCoordinates n =>
      sampledPrefix rate rewards C_star C_h e b w.1.val w.1.property n hn w.2) := by
  cases isEmpty_or_nonempty CellSource with
  | inl h =>
      let _ : IsEmpty CellSource := h
      exact measurable_of_empty _
  | inr h =>
      obtain ⟨x⟩ := h
      have hpos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e b x.val x.property
      have heb := x.property.1
      induction n with
      | zero =>
          have htrigger : e - 1 < b :=
            (Nat.sub_lt hpos (by decide : 0 < 1)).trans_le heb
          have hprojection : Measurable
              (fun w : CellSource × PrefixCoordinates 0 => (w.1, w.2.1)) :=
            measurable_fst.prodMk (measurable_fst.comp measurable_snd)
          have hbase := @measurable_collectionResidualSample p rate rewards C_star C_h e b (e - 1) htrigger
          have hcompose := hbase.comp hprojection
          convert hcompose using 1
          funext w
          exact sampledPrefix_zero rate rewards C_star C_h e b w.1.val w.1.property w.2
      | succ n ih =>
          have hk : e + n < b := by omega
          have hpair : Measurable (fun w : CellSource × PrefixCoordinates (n + 1) =>
                w.2.2 (Fin.last n)) :=
            (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
          have hprob := (measurable_collectionProposal rate rewards C_star C_h e b (e + n) hk).comp
            (measurable_fst : Measurable
              (Prod.fst : CellSource × PrefixCoordinates (n + 1) → CellSource))
          have hthreshold := measurableSet_lt
            (measurable_subtype_coe.comp (measurable_fst.comp hpair)) hprob
          have hfresh := (measurable_collectionResidualSample rate rewards C_star C_h e b
            (e + n) hk).comp (measurable_fst.prodMk (measurable_snd.comp hpair))
          have hrestriction : Measurable (fun w : CellSource × PrefixCoordinates (n + 1) =>
                (w.1, (w.2.1, fun i : Fin n => w.2.2 i.castSucc))) :=
            measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
              (measurable_pi_iff.mpr (fun i =>
                (measurable_pi_apply i.castSucc).comp (measurable_snd.comp measurable_snd))))
          have hprevious := (ih (Nat.le_of_succ_le hn)).comp hrestriction
          simpa only [sampledPrefix, DeferredRefreshUniformEvaluator.prefixValue,
            DeferredRefreshUniformKernels.sampleRecordedRefresh,
            FollowerCutoffScan.thresholdProposalBit, decide_eq_true_eq, Function.comp_def] using
            (Measurable.ite hthreshold hfresh hprevious)

/-- Joint Borelness of the full path, assembled from its coordinate evaluators. -/
theorem measurable_sampledPath_joint (n : ℕ) (hn : n ≤ b - e) :
    Measurable (fun w : CellSource × PrefixCoordinates n =>
      sampledPath rate rewards C_star C_h e b w.1.val w.1.property n hn w.2) := by
  let projection (i : Fin (n + 1)) :
      CellSource × PrefixCoordinates n → CellSource × PrefixCoordinates i.val :=
    fun w => (w.1, (w.2.1, fun j => w.2.2 ⟨j.val, by omega⟩))
  let evaluator (i : Fin (n + 1)) :
      CellSource × PrefixCoordinates i.val → CanonicalOrientedSetLaw.SlowSet p.K p.m :=
    fun w => sampledPrefix rate rewards C_star C_h e b w.1.val w.1.property i.val (by omega) w.2
  have hp (i : Fin (n + 1)) : Measurable (projection i) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_pi_iff.mpr (fun _ =>
        (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))))
  have he (i : Fin (n + 1)) : Measurable (evaluator i) :=
    @measurable_sampledPrefix_joint p rate rewards C_star C_h e b i.val (by omega)
  have h := measurable_pi_iff.mpr (fun i => (he i).comp (hp i))
  exact h

/-- The actual whole-array path is Borel jointly with the original source. -/
theorem measurable_sampledArrayPath_joint (n : ℕ) (hn : n ≤ b - e) :
    Measurable (fun w : CellSource × AuxiliaryArray p =>
      sampledArrayPath rate rewards C_star C_h e b w.1.val w.1.property n hn w.2) := by
  let evaluator : CellSource × PrefixCoordinates n →
      (Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m) :=
    fun w => sampledPath rate rewards C_star C_h e b w.1.val w.1.property n hn w.2
  let projection : CellSource × AuxiliaryArray p → CellSource × PrefixCoordinates n :=
    fun w => (w.1, actualPrefixCoordinates rate rewards C_star C_h e b w.1 n hn w.2)
  have he : Measurable evaluator :=
    @measurable_sampledPath_joint p rate rewards C_star C_h e b n hn
  have hp : Measurable projection := measurable_fst.prodMk
    (@measurable_actualPrefixCoordinates_joint p rate rewards C_star C_h e b n hn)
  have h := he.comp hp
  simpa only [evaluator, projection, Function.comp_def, sampledArrayPath] using h

/-- The unnormalized original-source law on the literal prefix event. -/
def prefixSourceLaw : MeasureTheory.Measure CellSource :=
  (sourceInputLaw p).comap Subtype.val

/-- The source restriction is literal; no positive-mass normalization occurs. -/
theorem prefixSourceLaw_map :
    (prefixSourceLaw rate rewards C_star C_h e b).map Subtype.val = (sourceInputLaw p).restrict
        (collectionPrefixCell rate rewards C_star C_h e b) :=
  map_comap_subtype_coe (measurableSet_collectionPrefixCell rate rewards C_star C_h e b) _

/-- The original-source/path test, excluding invalid cells without assigned values. -/
def jointPathEvent
    (Aset : Set (SourceInput p))
    (n : ℕ) (hn : n ≤ b - e)
    (B : Set (Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m)) :
    Set (SourceInput p × AuxiliaryArray p) :=
  Prod.map (Subtype.val : CellSource → SourceInput p) id ''
    {w : CellSource × AuxiliaryArray p | w.1.val ∈ Aset ∧
        sampledArrayPath rate rewards C_star C_h e b w.1.val w.1.property n hn w.2 ∈ B}

private theorem original_product_image
    (E : Set (CellSource × AuxiliaryArray p))
    (hE : MeasurableSet E) :
    ((sourceInputLaw p).prod (auxiliaryUniformLaw p))
      (Prod.map (Subtype.val : CellSource → SourceInput p) id '' E) =
      ((prefixSourceLaw rate rewards C_star C_h e b).prod (auxiliaryUniformLaw p)) E := by
  let inclusion := Prod.map
    (Subtype.val : CellSource → SourceInput p)
    (id : AuxiliaryArray p → _)
  have hi : MeasurableEmbedding inclusion :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_collectionPrefixCell rate rewards C_star C_h e b)).prodMap
        MeasurableEmbedding.id
  have hmap : (((prefixSourceLaw rate rewards C_star C_h e b).prod
      (auxiliaryUniformLaw p)).map inclusion) = ((sourceInputLaw p).prod
        (auxiliaryUniformLaw p)).restrict
          (collectionPrefixCell rate rewards C_star C_h e b ×ˢ Set.univ) := by
    rw [← MeasureTheory.Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
      prefixSourceLaw_map, MeasureTheory.Measure.map_id,
      MeasureTheory.Measure.restrict_prod_eq_prod_univ]
  have himage := hi.measurableSet_image.mpr hE
  have hsub : inclusion '' E ⊆ collectionPrefixCell rate rewards C_star C_h e b ×ˢ Set.univ := by
    rintro _ ⟨w, _, rfl⟩
    exact ⟨w.1.property, Set.mem_univ _⟩
  have h := congrArg (fun μ => μ (inclusion '' E)) hmap
  rw [MeasureTheory.Measure.map_apply hi.measurable himage,
    hi.injective.preimage_image, MeasureTheory.Measure.restrict_apply himage,
    Set.inter_eq_left.mpr hsub] at h
  exact h.symm

/-- Every finite-path cylinder has its literal Markov mass jointly with any
Borel test of the whole original source, without normalization. -/
theorem sampledArrayPath_joint_test
    (Aset : Set (SourceInput p)) (hA : MeasurableSet Aset)
    (n : ℕ) (hn : n ≤ b - e)
    (V : Fin (n + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    ((sourceInputLaw p).prod (auxiliaryUniformLaw p))
      (jointPathEvent rate rewards C_star C_h e b Aset n hn {V}) = ∫⁻ x : CellSource,
        (Subtype.val ⁻¹' Aset).indicator
          (fun x => pathAtom rate rewards C_star C_h e b x.val x.property n hn V) x
        ∂(prefixSourceLaw rate rewards C_star C_h e b) := by
  let E : Set (CellSource × AuxiliaryArray p) :=
    {w | w.1.val ∈ Aset ∧
      sampledArrayPath rate rewards C_star C_h e b w.1.val w.1.property n hn w.2 ∈ ({V} : Set _)}
  have hE : MeasurableSet E :=
    (hA.preimage (measurable_subtype_coe.comp measurable_fst)).inter
      ((measurableSet_singleton V).preimage
        (measurable_sampledArrayPath_joint rate rewards C_star C_h e b n hn))
  rw [jointPathEvent, original_product_image rate rewards C_star C_h e b E hE,
    MeasureTheory.Measure.prod_apply hE]
  apply MeasureTheory.lintegral_congr
  intro x
  by_cases hx : x.val ∈ Aset
  · rw [Set.indicator_of_mem (show x ∈ Subtype.val ⁻¹' Aset from hx)]
    simp only [E, Set.preimage_ofPred_eq, hx, true_and]
    change (auxiliaryUniformLaw p)
      (sampledArrayPath rate rewards C_star C_h e b x.val x.property n hn ⁻¹' {V}) = _
    rw [← MeasureTheory.Measure.map_apply
      (measurable_sampledArrayPath rate rewards C_star C_h e b x.val x.property n hn)
      (measurableSet_singleton V), sampledArrayPath_map,
      MeasureTheory.Measure.map_apply
        (measurable_sampledPath rate rewards C_star C_h e b x.val x.property n hn)
        (measurableSet_singleton V), Set.preimage_singleton]
    exact sampledPath_cylinder_measure rate rewards C_star C_h e b x.val x.property n hn V
  · rw [Set.indicator_of_notMem (show x ∉ Subtype.val ⁻¹' Aset from hx)]
    simp only [E, Set.preimage_ofPred_eq, hx, false_and, Set.ofPred_false,
      MeasureTheory.measure_empty]

end Bandits.Support.ReferenceActualCollectionHiddenRefreshPath

end
