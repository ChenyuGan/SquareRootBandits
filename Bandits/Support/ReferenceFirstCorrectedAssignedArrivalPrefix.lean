/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionCalendarNumericalJoin

/-!
# Observation-attributed arrivals at the first corrected installation

The projection below reads the selected payload and the actual prepared
follower configuration from each physical record. Prefix results retain the
same installed assignment and its original saved observations.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceFirstWindowNumericalStream ReferenceLaterLiveNumericalReadout
open ReferenceFollowerSparseEmissionRecovery ActiveFollowerQueueOperation
open RecordedQueueRun
open ReferenceCollectionSegmentExtraction ReferenceCollectionRawBufferHistory

namespace Bandits.Support.ReferenceFirstCorrectedAssignedArrivalPrefix

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem preparation_eq
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
  rw [r.output_eq]
  rfl

/-- The literal arrival attributed to one physical observation date. A
selection for another payload, a non-live selection, or an actual dagger slot
has no contribution. Ordinary slots use their actual prepared status; the
unoccupied case reads the saved candidate emitted on this date. -/
def attributedArrival? (P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (Bool × ℕ) := by
  classical
  let fi : ActiveRoundActions.Follower p.m :=
    ⟨i.val, i.isLt⟩
  match r.output.preparation.coordinator.selection with
  | none => exact none
  | some selected =>
      if hpayload : selected.view.payload = P then
        if hlive : CoordinatorLocalArmChoice.assignmentIsLive P selected.view.cutoff r.input.time then
          match (r.output.preparation.followers.followers i).configuration with
          | .dagger => exact none
          | .ordinary state _ =>
              exact some (true,
                if state.status = .unoccupied then
                  ReferenceFollowerSparseEmissionRecovery.emissionContribution
                    (P.downRecord fi) i r
                else
                  ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
                    (P.downRecord fi)
                    (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m fi)).2)
        else exact none
      else exact none

/-- If the record's actual live readout selects this payload, its projected
slot is present and equals the physical observation's quantized arrival. -/
theorem attributedArrival?_eq_of_laterLiveReadout
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k) = some c)
    (hselected : ∃ selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).input,
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).output.preparation.coordinator.selection =
        some selected ∧ selected.view.payload = P) :
    attributedArrival? (p := p) (rate := rate) P i
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k) =
      some (c.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
        (P.assignment.assigned
          (⟨i.val, i.isLt⟩ : ActiveRoundActions.Follower p.m))) := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).get k
  let fi : ActiveRoundActions.Follower p.m :=
    ⟨i.val, i.isLt⟩
  have hfi : fi = i := by
    apply Fin.ext
    rfl
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r c hc
  obtain ⟨selected', hselected', hpayload'⟩ := hselected
  have hselectedEq : selected' = selected := Option.some.inj (hselected'.symm.trans hselection)
  subst selected'
  have hpayload : selected.view.payload = P := hpayload'
  obtain ⟨cell, _hinput, henabled, _htrace, _henabledTrace, _hrows, _hrowIndex,
    _hrewards, _hmarker, _hlastDown, _howner, hoccupied, hunoccupied,
    _hlogging, _hrecording, _hcollection⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
      rate rewards C_star C_h source k c hc
  have hordinary : (r.output.preparation.followers.followers i).configuration =
      .ordinary (cell.states i) (cell.memories i) := cell.ordinary i
  have hsel : r.output.preparation.coordinator.selection = some selected := hselection
  have hcellSelected : cell.selected = selected :=
    Option.some.inj (cell.selection_actual.symm.trans hsel)
  have hliveP : CoordinatorLocalArmChoice.assignmentIsLive P selected.view.cutoff r.input.time := by
    simpa only [hpayload] using hlive
  change attributedArrival? (p := p) (rate := rate) P i r =
    some (c.enabled, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (P.assignment.assigned fi))
  unfold attributedArrival?
  simp only [hsel, dite_eq_left hpayload, dite_eq_left hliveP, hordinary]
  by_cases hunocc : (cell.states i).status = .unoccupied
  · have hcontribution := hunoccupied i hunocc
    have hem : ReferenceFollowerSparseEmissionRecovery.emissionContribution
        (P.downRecord fi) i r =
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (P.assignment.assigned fi) := by
      have hsaved := ReferenceFirstLiveUnoccupiedEmission.actualCurrentSavedContribution_eq_emissionContribution
        r P i
      have hphysical := hcontribution
      rw [hcellSelected, hpayload] at hphysical
      have hcombined := hsaved.symm.trans hphysical
      simpa only [fi, ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hcombined
    simp only [hunocc, ite_true, henabled]
    exact congrArg (fun n => some (true, n)) hem
  · have hcontribution := (hoccupied i hunocc).2
    have hraw : ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
        (P.downRecord fi)
        (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m fi)).2 =
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (P.assignment.assigned fi) := by
      simpa [r, fi, ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount,
        hcellSelected, hpayload] using hcontribution
    simp only [hunocc, ite_false, henabled]
    exact congrArg (fun n => some (true, n)) hraw

private theorem mapM_take_some_of_getElem
    {α β γ : Type*} (xs : List α) (ys : List β)
    (f : α → Option γ) (g : β → γ)
    (hlen : xs.length = ys.length)
    (hpoint : ∀ j (hj : j < xs.length),
      f (xs[j]'hj) = some (g (ys[j]'(by omega)))) :
    ∀ n, (xs.take n).mapM f = some ((ys.take n).map g) := by
  intro n
  induction n generalizing xs ys hlen hpoint with
  | zero => simp
  | succ n ih =>
      cases xs with
      | nil =>
          cases ys <;> simp at hlen ⊢
      | cons x xs =>
          cases ys with
          | nil => simp at hlen
          | cons y ys =>
              have htailLen : xs.length = ys.length := by simpa using hlen
              have hhead : f x = some (g y) := by
                have hh := hpoint 0 (by simp)
                change f x = some (g y) at hh
                exact hh
              have htail (j : ℕ) (hj : j < xs.length) :
                  f (xs[j]'hj) = some (g (ys[j]'(by omega))) := by
                have := hpoint (j + 1) (by simpa using Nat.succ_lt_succ hj)
                simpa only [List.getElem_cons_succ] using this
              have hrec := ih xs ys htailLen htail
              simp only [List.take_succ_cons, List.map_cons, List.mapM_cons,
                hhead, hrec]
              simp

/-- The actual later-choice installation and its saved initial queues and
follower bases, all read from the first corrected birth. -/
private theorem firstCell_corrected_installation_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate) (base : Fin (p.m - 1) → ℕ),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧
      ReferenceCollectionPhaseHistory.laterChosen birth.input = true ∧ c.enabled = true ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      c.rate = P.rate ∧
      c.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
      (∀ a : Fin p.K,
        P.queues a = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i : Fin (p.m - 1),
        base i = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
          (P.assignment.assigned i)).1 ∧
        (P.downRecord i).val.q =
          (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
            (P.assignment.assigned i)).2) := by
  classical
  dsimp only
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, _hbtime, henabled,
    hb, hrecord, htime, _hrows, _hselected, _hrewards, hmatch, _hsuccessor⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  have hbody := hmatch
  cases hprep : birth.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hlocal clockData installed selection =>
          simp only [hprep] at hbody
          rcases hbody with ⟨_, _, _, _, hSigma, _, _, _, hAll, hfollowers,
            _, hrate, hreward, _, _, _⟩
          let P : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
          let base : Fin (p.m - 1) → ℕ := installed.retainedBaseScore
          have hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P := by
            simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, P, hprep]
            exact ⟨rfl, (congrArg Fin.val hSigma).trans (congrArg Fin.val htime.symm)⟩
          have hqueues (a : Fin p.K) : P.queues a =
              (UnstoppedRecordedQueueComparison.unstoppedReplay
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 := by
            exact (hAll a).2.2.2
          have hbase (i : Fin (p.m - 1)) :
              base i = (UnstoppedRecordedQueueComparison.unstoppedReplay
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
                (P.assignment.assigned i)).1 ∧
              (P.downRecord i).val.q =
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
                  (P.assignment.assigned i)).2 := by
            change installed.retainedBaseScore i =
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
                  (installed.registers.payload.assignment.assigned i)).1 ∧
              (installed.registers.payload.downRecord i).val.q =
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
                  (installed.registers.payload.assignment.assigned i)).2
            exact hfollowers i
          have hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true := by
            simp only [ReferenceCollectionPhaseHistory.laterChosen,
              ← preparation_eq birth, hprep]
          refine ⟨L, c, birth, P, base, hL, hc, hprefix, hLb, hb, hrecord,
            htime, hchosen, henabled, hborn, hSigma, hrate, hreward, hqueues, hbase⟩
      | _ =>
          simp only [hprep] at hbody
  | _ =>
      simp only [hprep] at hbody

private theorem firstCell_birth_selected_payload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some birth)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen birth.input = true)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P) :
    ∃ selected : ReferenceActivePhysicalStep.Selection birth.input,
      birth.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = P := by
  classical
  obtain ⟨n, birth0, theta, _hb0, _ht0, hactual, _hcall, _hrows,
    _hselected, _hrewards, hreal⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_realization
      rate rewards C_star C_h u t z hz.1
  have heq : birth0 = birth := Option.some.inj (hactual.symm.trans hrecord)
  subst birth0
  cases hprep : birth.output.preparation.coordinator with
  | first outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen,
        ← preparation_eq birth, hprep] at hchosen
      cases hchosen
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hlocal clockData installed selection =>
          simp only [hprep] at hreal
          obtain ⟨_, _, cell, _, _, _, hcellPayload, _, _, _, _, _, _, _,
            _, _, _, _, _, _, _⟩ := hreal
          have hborn' : P = installed.registers.payload ∧
              P.sigma.val = birth.input.time.val := by
            simpa [ReferenceAssignmentPayloadPersistence.InstallationBirth, hprep] using hborn
          refine ⟨cell.selected, ?_, ?_⟩
          · simpa only [hprep] using cell.selection_actual
          · have hP := hborn'.1
            rw [hP]
            exact hcellPayload
      | _ => simp_all [ReferenceAssignmentPayloadPersistence.InstallationBirth]
  | live registers owned base outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen,
        ← preparation_eq birth, hprep] at hchosen
      cases hchosen
  | invalidCollectionCutoff =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen,
        ← preparation_eq birth, hprep] at hchosen
      cases hchosen
  | dagger =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen,
        ← preparation_eq birth, hprep] at hchosen
      cases hchosen

private theorem source_record_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get k
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h + k.val ∧
    r.input.rows = z.1.2 ∧
    r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
    r.input.rewards = rewards := by
  obtain ⟨_hc, _hspan, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  dsimp only
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every retained date from the corrected birth through any finite LIVE
prefix has a total assigned-arm observation word. The terminal branch uses
only the birth record, so it needs no successor record. -/
theorem firstCell_total_assigned_arrival_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate) (base : Fin (p.m - 1) → ℕ),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧
      birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (∀ j : Fin R.length,
        (R.get j).input.time.val = s + j.val ∧
        (R.get j).input.rows = z.1.2 ∧
        (R.get j).input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        (R.get j).input.rewards = rewards) ∧
      ReferenceCollectionPhaseHistory.laterChosen birth.input = true ∧ c.enabled = true ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      c.rate = P.rate ∧
      c.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
      (∀ a : Fin p.K, P.queues a =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i : Fin (p.m - 1),
        base i = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
          (P.assignment.assigned i)).1 ∧
        (P.downRecord i).val.q =
          (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
            (P.assignment.assigned i)).2) ∧
      (t.val + 1 = p.T → b + 1 = R.length) ∧
      (∀ _hterminal : t.val + 1 = p.T, ∀ i : Fin (p.m - 1),
        [birth].mapM (attributedArrival? (p := p) (rate := rate) P i) =
          some [(true, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            (P.assignment.assigned i))]) ∧
      (∀ _hq : t.val + 1 < p.T,
        ∃ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout)
          (beta : Fin (p.m - 1) → ℕ),
          birth.output.next.coordinator = .live rout qout beta ∧
          ∃ (hk : b + 1 < R.length)
            (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
            (hlater : s < rout.payload.sigma.val),
            let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b + 1)
            let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
              rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
            ∃ hB : B.length = W.length,
            (∀ i : Fin (p.m - 1), ∀ v : ℕ, 1 ≤ v → v ≤ 1 + W.length →
              ((birth :: W).take v).mapM
                (attributedArrival? (p := p) (rate := rate) P i) =
                some ((([c] ++ B.take (v - 1)).map fun cell =>
                  (cell.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                    (P.assignment.assigned i))))) ∧
            let e := b + 1 + W.length
            e ≤ R.length ∧
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h (s + e) z = some ((L ++ [c]) ++ B) ∧
            (R.drop b).take (1 + W.length) = birth :: W ∧
            (∀ j : Fin W.length,
              (W[j.val]).input.time.val = t.val + 1 + j.val ∧
              ReferenceLaterLiveNumericalReadout.laterLiveReadout s W[j.val] =
                some (B[j.val]'(by omega)) ∧
              ReferenceFirstCollectionCurrentRetainedGate.cell0 rate W[j.val] =
                some (B[j.val]'(by omega))) ∧
            ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
              (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
              rE.payload = P ∧
              (∀ he : e < R.length, R[e].input.state.coordinator = .live rE qE beta) ∧
              (e = R.length ∨
                ∃ (he : e < R.length) (seg : Segment rate) (I : Initializer p)
                  (l0 : Ledger rate) (c_cut : RecordedQueueRun.RoundInput p.K),
                  segmentAt R e = some seg ∧ seg.entry = R[e] ∧
                  seg.context.payload = P ∧ seg.context.preLedger = l0 ∧
                  seg.context.initializer = some I ∧
                  I = cutoffInitializer (liveRegistersAt rE R[e].input.time)
                    (liveOwnedAt rE qE R[e].input.time) beta R[e].input.time ∧
                  I.checkedStart rate = .success l0 ∧
                  I.assignment.arm = P.assignment.assigned ∧
                  I.sigma = t.val + 1 ∧ I.cutoff = s + e + 1 ∧
                  I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
                  I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
                  ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
                  (∃ during, seg.records = seg.entry :: during) ∧
                  seg.records ++ seg.remaining = R.drop e ∧
                  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
                    rate rewards C_star C_h (s + e + 1) z = some (((L ++ [c]) ++ B) ++ [c_cut]) ∧
                  R[e].input.time.val = s + e ∧
                  R[e].input.rows = z.1.2 ∧
                  R[e].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                  R[e].input.rewards = rewards ∧
                  ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[e] = some c_cut ∧
                  ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s R[e] = some c_cut ∧
                  c_cut.enabled = ReferenceActivePhysicalStep.collectionEnabled l0 R[e].input.time ∧
                  c_cut.rate = P.rate ∧
                  c_cut.reward = (fun a => ((rewards R[e].input.time a).val : ℝ) / (D p : ℝ)) ∧
                  (c_cut.enabled = false → c_cut.recordedArm = none ∧ ∀ a,
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c_cut a = 0) ∧
                  (∀ a, physicalQueueRecord l0 a R[e] = (c_cut.enabled,
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c_cut a)) ∧
                  ∀ i : Fin (p.m - 1),
                    Option.map (fun word => word ++
                      [physicalQueueRecord l0 (P.assignment.assigned i) R[e]])
                      ((birth :: W).mapM (attributedArrival? (p := p) (rate := rate) P i)) =
                    some ((([c] ++ B) ++ [c_cut]).map fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
                        (P.assignment.assigned i))))) := by
  classical
  intro R s b
  obtain ⟨L, c, birth, P, base, hL, hc, hinputs, hLb, hb, hrecord,
    htime, hchosen, henabled, hborn, hSigma, hrate, hreward, hqueues, hbase⟩ :=
    firstCell_corrected_installation_seed rate rewards C_star C_h u t z hz
  have hreadBirth : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) birth = some c := by
    simpa only [ReferenceFirstCollectionCurrentNumericalCell.currentCell,
      hrecord, Option.bind_some] using hc
  obtain ⟨birthSelection, hselectedBirth, hpayloadBirth⟩ :=
    firstCell_birth_selected_payload rate rewards C_star C_h u t z hz
      birth P hrecord hchosen hborn
  have hbirthIndex : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  let kb : Fin R.length := ⟨b, hbirthIndex⟩
  have hbirthGet : R.get kb = birth := by
    have hget : R[b]? = some (R[b]'hbirthIndex) := List.getElem?_eq_getElem hbirthIndex
    rw [hb] at hget
    have heq := Option.some.inj hget
    simpa only [List.get_eq_getElem, kb, Fin.val_mk] using heq.symm
  have hbirthGetExact :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get kb = birth := by
    simpa only [R] using hbirthGet
  have hreadBirthGet : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) (R.get kb) = some c := by
    rw [hbirthGet]
    exact hreadBirth
  have hselectedBirthGet : ∃ selected : ReferenceActivePhysicalStep.Selection (R.get kb).input,
      (R.get kb).output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = P := by
    rw [hbirthGet]
    exact ⟨birthSelection, hselectedBirth, hpayloadBirth⟩
  have hsourceBirth := source_record_data rate rewards C_star C_h z kb
  rw [hbirthGetExact] at hsourceBirth
  obtain ⟨hdateBirth, hrowsBirth, hselectedSourceBirth, hrewardBirth⟩ := hsourceBirth
  refine ⟨L, c, birth, P, base, hL, hc, hinputs, hLb, hb, hrecord, htime,
    hrowsBirth, hselectedSourceBirth, hrewardBirth,
    (fun j => source_record_data rate rewards C_star C_h z j), hchosen, henabled, hborn,
    hSigma, hrate, hreward, hqueues, hbase, ?_, ?_, ?_⟩
  · intro hterminal
    have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hdate : s + b = t.val := by
      simpa only [s, kb, Fin.val_mk, htime] using hdateBirth.symm
    change R.length = p.T - s at hRlen
    omega
  · intro hterminal i
    have hprojection := attributedArrival?_eq_of_laterLiveReadout
      rewards C_star C_h z kb P i c hreadBirthGet hselectedBirthGet
    rw [hbirthGetExact] at hprojection
    have hprojectionBirth : attributedArrival? (p := p) (rate := rate) P i birth =
        some (true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
          (P.assignment.assigned i)) := by
      simpa only [henabled, ActiveRoundActions.Follower,
        PublicDiscreteDraws.followerCount] using hprojection
    simp [List.mapM_cons, hprojectionBirth]
  · intro hq
    obtain ⟨birthR, rout, qout, beta, hbR, _hstart, _htime, _hrows,
      _hselected, _hrewards, hbornR, _hsigmaR, hlater, hnext, hcontinuation⟩ :=
      ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
        rate rewards C_star C_h u t z hz
    have hbirthEq : birthR = birth := Option.some.inj (hbR.symm.trans hb)
    subst birthR
    have hroute : P = rout.payload :=
      ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
        birth P rout.payload hborn hbornR
    have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hk : b + 1 < R.length := by
      rw [hRlen]
      have hsigma := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
        birth P hborn
      change s + b = t.val at _hstart
      omega
    have hbIndex' : b < R.length := by omega
    have hbGet' : R[b]'hbIndex' = birth := by
      have hh : R[b]? = some (R[b]'hbIndex') := List.getElem?_eq_getElem hbIndex'
      rw [hb] at hh
      exact (Option.some.inj hh).symm
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      rewards C_star C_h z b hk
    have hstate : R[b + 1].input.state.coordinator = .live rout qout beta := by
      rw [hbGet'] at hadj
      have hcoord := congrArg (fun state => state.coordinator) hadj
      simpa only [hnext] using hcoord
    refine ⟨rout, qout, beta, hnext, hk, hstate, hlater, ?_⟩
    dsimp only
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let k : Fin R.length := ⟨b + 1, hk⟩
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z k rout qout beta hstate hlater
    have hBlen : B.length = W.length := by
      dsimp [B, W, k]
      exact ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_length
        rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
    have hwords : ∀ i : Fin (p.m - 1), ∀ v : ℕ, 1 ≤ v → v ≤ 1 + W.length →
        ((birth :: W).take v).mapM
          (attributedArrival? (p := p) (rate := rate) P i) =
          some (([c] ++ B.take (v - 1)).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
              (P.assignment.assigned i))) := by
      intro i v hvpos hvlen
      have hpoint (j : ℕ) (hj : j < W.length) :
          attributedArrival? (p := p) (rate := rate) P i (W[j]'hj) =
            some ((B[j]'(by omega)).enabled,
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (B[j]'(by omega)) (P.assignment.assigned i)) := by
        let ji : Fin W.length := ⟨j, hj⟩
        have hstep := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_step
          rewards C_star C_h z k rout qout beta hstate hlater ji
        dsimp only [W, k, B] at hstep
        rcases hstep with ⟨rv, qv, hp, _hstepState, serviced, finished,
          _hreadStep, _henabled, _hreward, _hrate, hcanonical, _hrecord,
          _hfailure, _harrivals, _hnext⟩
        obtain ⟨selected, _ho, hselection, hselectedPayload, _hcell⟩ := hcanonical
        have hselectedP : selected.view.payload = P := by
          exact hselectedPayload.trans hroute.symm
        have hindex := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
          rewards C_star C_h z k j hj
        have hlenW := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le
          rewards C_star C_h z ⟨b + 1, hk⟩
        have hlenW' : b + 1 +
            (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b + 1)).length ≤ R.length := by
          simpa only [Fin.val_mk] using hlenW
        have hjW : j < (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b + 1)).length := by
          simpa only [W] using hj
        have hkj : b + 1 + j < R.length := by omega
        let kj : Fin R.length := ⟨b + 1 + j, hkj⟩
        have hrecordEq : R.get kj = W[j]'hj := by
          simpa only [List.get_eq_getElem, kj, Fin.val_mk, W, k] using hindex.symm
        have hreadCell := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_readout
          rewards C_star C_h z k rout qout beta hstate hlater ji
        have hreadCell' : ReferenceLaterLiveNumericalReadout.laterLiveReadout
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
            (R.get kj) = some (B[j]'(by omega)) := by
          rw [hrecordEq]
          simpa only [W, B, ji, Fin.val_mk] using hreadCell
        have hselection' : (R.get kj).output.preparation.coordinator.selection = some selected := by
          simpa only [List.get_eq_getElem, kj, ji, Fin.val_mk] using hselection
        have hprojection := attributedArrival?_eq_of_laterLiveReadout
          rewards C_star C_h z kj P i (B[j]'(by omega)) hreadCell'
          ⟨selected, hselection', hselectedP⟩
        rw [hrecordEq] at hprojection
        simpa only [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hprojection
      have htail := mapM_take_some_of_getElem W B
        (attributedArrival? (p := p) (rate := rate) P i)
        (fun cell => (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
          (P.assignment.assigned i))) hBlen.symm hpoint (v - 1)
      have hbirthProjection := attributedArrival?_eq_of_laterLiveReadout
        rewards C_star C_h z kb P i c hreadBirthGet hselectedBirthGet
      rw [hbirthGetExact] at hbirthProjection
      have htake : (birth :: W).take v = birth :: W.take (v - 1) := by
        cases v with
        | zero => omega
        | succ v => simp
      have hbirthProjection' : attributedArrival? (p := p) (rate := rate) P i birth =
          some (true, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            (P.assignment.assigned i)) := by
        simpa only [henabled, ActiveRoundActions.Follower,
          PublicDiscreteDraws.followerCount] using hbirthProjection
      rw [htake, List.mapM_cons, hbirthProjection', htail]
      simp [B, k, henabled]
    refine ⟨hBlen, hwords, ?_⟩
    obtain ⟨LG, cG, birthG, hLG, hcG, _hprefixG, _hLbG, _hdateG, hbG,
      _htG, _hrowsG, _hselectedG, _hrewardsG, _henabledG, _hreadG, _hcellG,
      _hmodeG, hcontG⟩ :=
      ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
        rate rewards C_star C_h u t z hz
    have hLG' : LG = L := Option.some.inj (hLG.symm.trans hL)
    have hcG' : cG = c := Option.some.inj (hcG.symm.trans hc)
    have hbG' : birthG = birth := Option.some.inj (hbG.symm.trans hb)
    subst LG cG birthG
    obtain ⟨_hsigmaG, htailG⟩ := hcontG rout qout beta hnext
    obtain ⟨hkG, hstateG, hlaterG, _hlenG, heR, _heT, _hAlen, _hAdate,
      hprefixA, hwindow, hdates, rE, qE, hpE, hstateE, hboundary⟩ := htailG hq
    refine ⟨heR, hprefixA, hwindow, hdates, rE, qE, hpE.trans hroute.symm,
      hstateE, ?_⟩
    rcases hboundary with hhor | ⟨he, seg, I, l0, hseg, hentry, hpay, hpre, hI,
      hIdef, hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbeta, hcut,
      hnonempty, hpartition, D, hD, hcells, _hphysicalWords, _hrest⟩
    · exact Or.inl hhor
    · obtain ⟨during, hduring⟩ := hnonempty
      have hpos : 0 < seg.records.length := by rw [hduring]; simp only [List.length_cons]; omega
      let j0 : Fin seg.records.length := ⟨0, hpos⟩
      let c_cut := D[0]'(by omega)
      have hhead : seg.records[0]'hpos = R[b + 1 + W.length]'he := by
        have hh : seg.records[0]? = some seg.entry := by rw [hduring]; rfl
        have hget : seg.records[0]? = some (seg.records[0]'hpos) :=
          List.getElem?_eq_getElem hpos
        exact (Option.some.inj (hget.symm.trans hh)).trans hentry
      obtain ⟨hcell0, done, _hextract, _hunoccupied, hreadCut, _hpayDone,
        _hsigmaDone, _hcutDone, _hfreezeDone, henabledCut, _hdateCut,
        hrateCut, hrewardCut, _hrowsCut, _hselectedCut, _hrewardsCut,
        out, _hcallCut, _hrunCut, _hrecordCut, _hgateCut, _hrawCut,
        _harrivalCut, _hphysicalCut, hdisabledCut, hphysicalRaw⟩ := hcells j0
      change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[0] = some c_cut at hcell0
      change ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s seg.records[0] = some c_cut at hreadCut
      change c_cut.enabled = ReferenceActivePhysicalStep.collectionEnabled l0 seg.records[0].input.time at henabledCut
      change c_cut.rate = rout.payload.rate at hrateCut
      change c_cut.reward = (fun a => ((rewards seg.records[0].input.time a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) at hrewardCut
      change c_cut.enabled = false → c_cut.recordedArm = none ∧ ∀ a,
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c_cut a = 0 at hdisabledCut
      change ∀ a, physicalQueueRecord l0 a seg.records[0] =
        (c_cut.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c_cut a) at hphysicalRaw
      rw [hhead] at hcell0 hreadCut henabledCut hrewardCut hphysicalRaw
      have hrecordCut :
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
            rate rewards C_star C_h z)[s + (b + 1 + W.length) -
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                rate rewards C_star C_h z]? = some (R[b + 1 + W.length]'he) := by
        change R[s + (b + 1 + W.length) - s]? = _
        rw [Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem he
      have hprefixCut := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
        rate rewards C_star C_h (s + (b + 1 + W.length)) z ((L ++ [c]) ++ B)
        hprefixA (R[b + 1 + W.length]'he) c_cut hrecordCut hcell0
      have hsourceCut := source_record_data rate rewards C_star C_h z
        ⟨b + 1 + W.length, he⟩
      obtain ⟨hdateSourceCut, hrowsSourceCut, hselectedSourceCut, hrewardSourceCut⟩ := hsourceCut
      refine Or.inr ⟨he, seg, I, l0, c_cut, hseg, hentry, hpay.trans hroute.symm,
        hpre, hI, hIdef, hchecked, ?_, hIsigma, hIcut, ?_, hfreeze, hbeta,
        hcut, ⟨during, hduring⟩, hpartition, hprefixCut, hdateSourceCut,
        hrowsSourceCut, hselectedSourceCut, hrewardSourceCut, hcell0, hreadCut, henabledCut, ?_,
        hrewardCut, hdisabledCut, hphysicalRaw, ?_⟩
      · simpa only [hroute] using harm
      · simpa only [hroute] using hIscan
      · simpa only [hroute] using hrateCut
      · intro i
        have hfull := hwords i (1 + W.length) (by omega) le_rfl
        have htake : (birth :: W).take (1 + W.length) = birth :: W := by
          apply List.take_of_length_le
          simp only [List.length_cons]
          omega
        rw [htake] at hfull
        have htakeB : B.take (1 + W.length - 1) = B := by
          apply List.take_of_length_le
          omega
        rw [htakeB] at hfull
        rw [hfull, Option.map_some, hphysicalRaw]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rfl
end Bandits.Support.ReferenceFirstCorrectedAssignedArrivalPrefix

end
