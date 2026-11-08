/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionActiveBoundaryQueueQuery
public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint
public import Bandits.Support.ReferenceFirstCollectionRoundEndObservation

/-!
# Detected strict-past queue mask for first-collection tasks

The mask keeps actual incoming pending tasks only while the actual decoder
cutoff has not passed and the same active-boundary queue query is safe. It is
an analytical observation; it does not modify the physical protocol.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionDetectedQueueMask

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ}

/-- Literal finite union of actual active queue boundaries retained before
the actual decoder's strict-past cutoff. -/
def safePendingEvent (t : Fin p.T) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | t.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z ∧
    ∃ b : Fin (t.val + 1), ∃ v : Fin (t.val + 1),
      b.val ≤ v.val ∧ z ∈
        ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          b.val v.val t}

/-- The detected task set, extended by the empty analytical task outside the
physical horizon. -/
def Pdetect (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Finset (Fin (p.m - 1)) :=
  if hn : n < p.T then
    if z ∈ safePendingEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) ⟨n, hn⟩ then
      ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h n z
    else ∅
  else ∅

private theorem decoderFlagFalse_measurable_at
    (control0 : ContinuousLearningRows.TimeControl p) (n t : Fin p.T)
    (hnt : n.val ≤ t.val) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag
          rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) = false} := by
  have htrue :=
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_decoder_flag_true_adapted
      rate rewards C_star C_h control0 n
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at htrue
  rcases htrue with ⟨S, hS, hpre⟩
  let S' := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val) ⁻¹' S
  have hSfalse : MeasurableSet (S'ᶜ) :=
    hS.preimage (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
      control0 n.val) |>.compl
  have hfactor :
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹' S'ᶜ =
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag
            rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) = false} := by
    ext z
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) ∉ S ↔ _
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 n.val t.val hnt z]
    have hmem := congrArg (fun E : Set (BootstrapPrivateRoundStreams.SourceInput p) => z ∈ E) hpre
    have htrueAt : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val z ∈ S ↔
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag
          rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) = true := by
      simpa [Set.mem_preimage] using hmem
    cases ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag
        rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) <;> simp_all
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  exact (MeasurableSpace.measurableSet_comap).2 ⟨S'ᶜ, hSfalse, hfactor⟩

private theorem decoderKeep_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p | t.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
          rate rewards C_star C_h z} := by
  have hset :
      {z : BootstrapPrivateRoundStreams.SourceInput p | t.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
          rate rewards C_star C_h z} =
      ⋂ n : Fin (t.val + 1),
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag
            rate rewards C_star C_h z n.val
              (by have hn := n.isLt; omega) = false} := by
    ext z
    change (t.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
          rate rewards C_star C_h z) ↔ _
    rw [ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoder_cutoff_after_current_iff
      rate rewards C_star C_h t z]
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  apply MeasurableSet.iInter
  intro n
  let j : Fin p.T := ⟨n.val, by have hn := n.isLt; have ht := t.isLt; omega⟩
  exact decoderFlagFalse_measurable_at (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) control0 j t (by dsimp [j]; omega)

/-- The finite boundary union is visible at the exact pre-round source
field. Each queue query is one of A's actual whole-vector events. -/
theorem safePendingEvent_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (safePendingEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) t) := by
  have hboundary :
      safePendingEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) t =
      {z | t.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
            rate rewards C_star C_h z} ∩
        ⋃ b : Fin (t.val + 1), ⋃ v : Fin (t.val + 1),
          {z | b.val ≤ v.val ∧ z ∈
            ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
              (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
              b.val v.val t} := by
    ext z
    simp only [safePendingEvent, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iUnion]
  rw [hboundary]
  apply (decoderKeep_measurable (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) control0 t).inter
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro v
  by_cases hbv : b.val ≤ v.val
  · have hvt : v.val ≤ t.val := Nat.le_of_lt_succ v.isLt
    have hq :=
      ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_measurable
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        control0 b.val v.val t hbv hvt
    simpa [hbv] using hq
  · have hempty :
      {z : BootstrapPrivateRoundStreams.SourceInput p | b.val ≤ v.val ∧ z ∈
        ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          b.val v.val t} = ∅ := by
      ext z
      simp [hbv]
    rw [hempty]
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ
      control0 t.val]
    exact (MeasurableSpace.measurableSet_comap).2
      ⟨∅, MeasurableSet.empty, by ext z; simp⟩

/-- Task membership is measurable at exactly the requested pre-round field,
also on the empty extension beyond T. -/
theorem Pdetect_mem_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (n : ℕ) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p | i ∈
        Pdetect (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) n z} := by
  by_cases hn : n < p.T
  · let t : Fin p.T := ⟨n, hn⟩
    have hset :
        {z : BootstrapPrivateRoundStreams.SourceInput p | i ∈
          Pdetect (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) n z} =
        safePendingEvent (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) t ∩
          {z | i ∈ ReferenceFirstCollectionPendingObservation.Praw
            rate rewards C_star C_h n z} := by
      ext z
      by_cases hsafe : z ∈ safePendingEvent (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) t
      · simp [Pdetect, hn, t, hsafe]
      · simp [Pdetect, hn, t, hsafe]
    rw [hset]
    have ht : t.val + 1 = n + 1 := by rfl
    rw [← ht]
    exact (safePendingEvent_measurable (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) control0 t).inter
      (ReferenceFirstCollectionPendingObservation.Praw_mem_measurable
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        control0 i t)
  · have hset :
        {z : BootstrapPrivateRoundStreams.SourceInput p | i ∈
          Pdetect (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) n z} = ∅ := by
      ext z
      simp [Pdetect, hn]
    rw [hset]
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ
      control0 n]
    exact (MeasurableSpace.measurableSet_comap).2
      ⟨∅, MeasurableSet.empty, by ext z; simp⟩

/-- The detected mask only erases actual pending tasks. -/
theorem Pdetect_subset_Praw (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Pdetect (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      n z ⊆ ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h n z := by
  by_cases hn : n < p.T
  · simp only [Pdetect, dite_eq_left hn]
    split_ifs <;> simp
  · simp [Pdetect, hn]



private theorem boundary_parameters_unique
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s₀ u₀ s₁ u₁ : ℕ)
    (h₀ : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s₀ u₀ t)
    (h₁ : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s₁ u₁ t) :
    s₀ = s₁ ∧ u₀ = u₁ := by
  rcases h₀ with ⟨hs₀, r₀, hr₀, hstate₀⟩
  rcases h₁ with ⟨hs₁, r₁, hr₁, hstate₁⟩
  have hrs : r₀ = r₁ := Option.some.inj (hr₀.symm.trans hr₁)
  subst r₁
  have hs : s₀ = s₁ := hs₀.symm.trans hs₁
  refine ⟨hs, ?_⟩
  cases hc : r₀.input.state.coordinator with
  | first => simp [hc] at hstate₀
  | dagger => simp [hc] at hstate₀
  | live reg owned base =>
      simp only [hc] at hstate₀ hstate₁
      exact hstate₀.1.symm.trans hstate₁.1
  | collection payload ledger saved =>
      simp only [hc] at hstate₀ hstate₁
      omega

private theorem firstLiveWindow_cutoff
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length <
      records.length) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (records[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length]).input =
        true := by
  induction records with
  | nil => simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at hshort
  | cons r rs ih =>
      cases hc : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
      | false =>
          simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc] using
            ih (by simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc] using hshort)
      | true =>
          simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc]

/-- A nonempty actual incoming task is witnessed by the unique actual
collection-window boundary. The stream, suffix, and incoming records all use
the same original source and the same dispatch. -/
private theorem activeBoundary_of_Praw
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hP : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val z).Nonempty) :
    ∃ s u : ℕ,
      s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
      u = s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length ∧
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length <
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length ∧
      s ≤ u ∧ u ≤ t.val ∧
      z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
        rate rewards C_star C_h s u t := by
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceFirstCollectionPendingObservation.Praw_at,
      ReferenceFirstCollectionPendingObservation.Q_eq_empty_of_not_launchBy
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        t z hnot] at hP
    exact Finset.not_nonempty_empty hP
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hlaunch.1
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  have hspan := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
    rate rewards C_star C_h z
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) z rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h = E.records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      rate rewards C_star C_h z hcross
  have hloc : ∃ k : Fin B.length, B[k.val].input.time = t := by
    let observed := fun records : List
        (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
      ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
        (ReferenceCollectionPhaseHistory.collectionWindow records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t
    exact Eq.mp (congrArg observed hrecords)
      (ReferenceFirstCollectionPendingObservation.Praw_localization
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) t z hP)
  obtain ⟨k, htime⟩ := hloc
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hshort : w < count := by
    by_contra hnot
    have hB : B = [] := by
      simp only [B, ReferenceCollectionPhaseHistory.collectionWindow,
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w by omega),
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w + 1 by omega),
        List.take_nil, List.takeWhile_nil, List.append_nil]
    have hk := k.isLt
    have hlen : B.length = 0 := congrArg List.length hB
    omega
  obtain ⟨_, _, d, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
      rate rewards C_star C_h z hcross hshort
  let out := d.stream
  have hwindow : out.window = B := out.windowIsActual
  let kn : Fin out.window.length := ⟨k.val, by rw [hwindow]; exact k.isLt⟩
  have halign := out.alignment kn
  have hrecordIndex :
      E.records[w + k.val]? = some B[k.val] := by
    simpa only [E, w, kn, hwindow] using halign.1
  have hstart : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) z rewards C_star C_h = s := by
    rfl
  have htime' : B[k.val].input.time.val + 1 =
      ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h +
        w + 1 + k.val := by
    simpa only [kn, hwindow] using halign.2
  have hindex : t.val - s = w + k.val := by
    rw [htime, hstart] at htime'
    omega
  have hactualRecord :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some B[k.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left hlaunch.2, hrecords, hindex]
    exact hrecordIndex
  have hQ : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t z).Nonempty := by
    rw [ReferenceFirstCollectionPendingObservation.Praw_at] at hP
    exact hP
  have hQB : (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      s B[k.val].input.time z).Nonempty := by
    simpa only [htime] using hQ
  have hqwin :=
    ReferenceFirstCollectionPendingObservation.Q_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      z count hcross hspan hshort d k
  change ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      B[k.val].input.time z = _ at hqwin
  have hstartPhysical : s =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := rfl
  have hboundaryDate : t.val = s + w + k.val := by
    have htval : B[k.val].input.time.val = t.val := congrArg Fin.val htime
    rw [htval, hstart] at htime'
    omega
  have hwindowEq :
      w = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length := by
    rw [hrecords]
  have hshortR :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length <
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length := by
    rw [hrecords]
    change w < E.records.length
    rw [hcount]
    exact hshort
  have hu : s + w ≤ t.val := by omega
  have hs : s ≤ s + w := by omega
  by_cases hk0 : k.val = 0
  · have hB0 : B[k.val] = out.cutoff.cut := by
      simpa only [hwindow, hk0] using out.cutoffIsHead
    obtain ⟨execution⟩ := out.cutoffExecution
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen
        out.cutoff.cut.input = true := by
      have hat := out.cutoff.cutIndex
      have heq : E.records[w] = out.cutoff.cut :=
        (List.getElem?_eq_some_iff.mp hat).2
      have hw : w < E.records.length := by rw [hcount]; exact hshort
      rw [← heq]
      exact firstLiveWindow_cutoff E.records hw
    have hsigma : execution.live.payload.sigma.val = s := by
      rw [← execution.payloadIsLive]
      exact out.cutoffContext.2.1
    have hC : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
        rate rewards C_star C_h s (s + w) t := by
      refine ⟨rfl, B[k.val], hactualRecord, ?_⟩
      rw [hB0, execution.actualLive]
      refine ⟨?_, hsigma, ?_⟩
      · rw [hstart] at htime'
        have htime0' : t.val = s + w := by
          simpa [hk0] using hboundaryDate
        exact htime0'
      · exact hcut
    refine ⟨s, s + w, rfl, ?_, ?_, hs, hu, hC⟩
    · rw [hwindowEq]
    · exact hshortR
  · have hQwindow : ReferenceFirstCollectionPendingObservation.Q
      rate rewards C_star C_h s B[k.val].input.time z =
        if k.val = 0 then Finset.univ else
          if h : k.val < out.ell then
            (out.ledgers ⟨k.val - 1, by omega⟩).pending else ∅ := by
      simpa only [out] using hqwin
    have hkell : k.val < out.ell := by
      by_contra hnot
      rw [hQwindow, ite_eq_right hk0,
        dite_eq_right (Nat.not_lt.mpr (Nat.le_of_not_gt hnot))] at hQB
      exact Finset.not_nonempty_empty hQB
    obtain ⟨j, r, incoming, cell, _, hr, _, hprevious⟩ :=
      out.cell_at ⟨k.val, hkell⟩ (show 0 < k.val by omega)
    have hrEq : r = B[k.val] := by
      rw [hwindow] at hr
      exact (List.getElem?_eq_some_iff.mp hr).2.symm
    have hcoord := cell.readyInput.1
    rw [hrEq] at hcoord
    have hcutoff : incoming.cutoff = s + w + 1 := by
      rw [hprevious, (out.context ⟨k.val - 1, Nat.lt_of_le_of_lt
        (Nat.sub_le _ _) hkell⟩).2.1]
      simpa only [hstart] using out.cutoff.ledgerCutoff
    have hpayloadSigma : out.payload.sigma.val = s := by
      rw [out.payloadMatchesCutoff]
      exact out.cutoffContext.2.1.trans hstart
    have hpending : (out.ledgers ⟨k.val - 1, by omega⟩).pending.Nonempty := by
      rw [hQwindow] at hQB
      simpa [hk0, hkell] using hQB
    have hpendingIncoming : incoming.pending.Nonempty := by
      rw [hprevious]
      exact hpending
    have hC : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
        rate rewards C_star C_h s (s + w) t := by
      refine ⟨rfl, B[k.val], hactualRecord, ?_⟩
      rw [hcoord]
      refine ⟨by omega, hpayloadSigma, ?_, hpendingIncoming⟩
      simpa only [hstart] using hcutoff
    refine ⟨s, s + w, rfl, ?_, ?_, hs, hu, hC⟩
    · rw [hwindowEq]
    · exact hshortR

/-- Every nonempty incoming task is supported by an actual boundary, and
those boundaries are unique at a fixed source date. -/
theorem actual_pending_boundary_existsUnique
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
      t.val z).Nonempty ↔
    ∃! pair : ℕ × ℕ,
      pair.1 ≤ pair.2 ∧ pair.2 ≤ t.val ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
          rate rewards C_star C_h pair.1 pair.2 t := by
  constructor
  · intro hP
    obtain ⟨s, u, hs, hu, _hw, hsu, hut, hC⟩ :=
      activeBoundary_of_Praw (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) t z hP
    refine ⟨(s, u), ⟨hsu, hut, hC⟩, ?_⟩
    intro pair hp
    rcases pair with ⟨s', u'⟩
    rcases hp with ⟨hs', hu', hC'⟩
    have hsame := boundary_parameters_unique (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) t z s u s' u' hC hC'
    exact Prod.ext hsame.1.symm hsame.2.symm
  · rintro ⟨⟨s, u⟩, ⟨_, _, hC⟩, _⟩
    exact ReferenceFirstCollectionActiveBoundaryQueueQuery.C_subset_Praw
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      s u t hC

/-- The unique boundary pair is exactly the physical first start and the
first-live window's cutoff. -/
theorem actual_pending_boundary_window
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hP : (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h
      t.val z).Nonempty) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    ∃! pair : ℕ × ℕ,
      pair.1 ≤ pair.2 ∧ pair.2 ≤ t.val ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
          rate rewards C_star C_h pair.1 pair.2 t ∧
        pair.1 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
        pair.2 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + w ∧
        w < R.length := by
  dsimp only
  obtain ⟨s, u, hs, hu, hw, hsu, hut, hC⟩ :=
    activeBoundary_of_Praw (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) t z hP
  refine ⟨(s, u), ⟨hsu, hut, hC, hs, ?_, hw⟩, ?_⟩
  · calc
      u = s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length := hu
      _ = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)).length := by rw [hs]
  · intro pair hp
    rcases pair with ⟨s', u'⟩
    rcases hp with ⟨hs', hu', hC', _, _, _⟩
    have hsame := boundary_parameters_unique (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) t z s u s' u' hC hC'
    exact Prod.ext hsame.1.symm hsame.2.symm

/-- At an explicit actual boundary, the finite union selects exactly the
same queue field, subject to the actual strict-past decoder cutoff. -/
theorem safePendingEvent_at_boundary
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s u : ℕ) (hs : s ≤ u) (hu : u ≤ t.val)
    (hC : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s u t) :
    z ∈ safePendingEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) t ↔
      t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          s u t := by
  constructor
  · intro hsafe
    change t.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
          rate rewards C_star C_h z ∧
      ∃ b : Fin (t.val + 1), ∃ v : Fin (t.val + 1),
        b.val ≤ v.val ∧ z ∈
          ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
            (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
            b.val v.val t at hsafe
    rcases hsafe with ⟨hkeep, b, v, hbv, hq⟩
    change z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
        rate rewards C_star C_h b.val v.val t ∧ _ at hq
    have hsame := boundary_parameters_unique (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) t z s u b.val v.val hC hq.1
    have hq' := hq.2
    rw [← hsame.1, ← hsame.2] at hq'
    have hqueue : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t := by
      change z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
          rate rewards C_star C_h s u t ∧ _
      exact ⟨hC, hq'⟩
    exact ⟨hkeep, hqueue⟩
  · rintro ⟨hkeep, hq⟩
    refine ⟨hkeep, ⟨s, ?_⟩, ⟨u, ?_⟩, hs, hq⟩ <;> omega

/-- The detector's value on an actual active boundary is its same-field
pending set exactly when the strict-past decoder and queue tests both pass. -/
theorem Pdetect_at_boundary
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s u : ℕ) (hs : s ≤ u) (hu : u ≤ t.val)
    (hC : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
      rate rewards C_star C_h s u t) :
    Pdetect (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t.val z =
      if t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
          rate rewards C_star C_h z ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          s u t then
        ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t.val z
      else ∅ := by
  simp only [Pdetect, dite_eq_left t.isLt,
    safePendingEvent_at_boundary (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) t z s u hs hu hC]

/-- Same-field service for detected tasks under the original source law. -/
theorem Pdetect_service
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (i : Fin (p.m - 1)) (n : ℕ), n < p.T →
        i ∈ Pdetect (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) n z →
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          PhaseServiceWaiting.observation
            (ReferenceFirstCollectionRoundEndObservation.x
              (rate := rate) rewards C_star C_h) i n |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (n + 1)] z =
          ReferenceFirstCollectionRoundEndObservation.g rewards n z /
            (8 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
  filter_upwards [ReferenceFirstCollectionPendingObservation.Praw_service
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    control0] with z hz
  intro i n hn hi
  have hraw := Pdetect_subset_Praw (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) n z hi
  rw [ReferenceFirstCollectionRoundEndObservation.observation_eq_X
    (rate := rate) rewards C_star C_h i n hn]
  simpa [ReferenceFirstCollectionRoundEndObservation.g, hn] using
    hz i ⟨n, hn⟩ hraw

end Bandits.Support.ReferenceFirstCollectionDetectedQueueMask

end
