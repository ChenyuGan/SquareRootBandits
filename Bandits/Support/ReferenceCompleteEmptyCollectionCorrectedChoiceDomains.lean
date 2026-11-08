/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionCutoffLastServiceBounds
public import Bandits.Support.ReferenceCompleteContinuingCollectionChoiceDomains
public import Bandits.Support.BoundedScoreProductDomination

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Empty-pending corrected collection starts on the complete source

Internal numerical reconstruction and selection for an actual incoming collection
whose pending set is empty before its old grid boundary. The corrected law uses
the retained old anchor and the literal signed masses, on every complete
assignment vector. Source evidence: ZIP4 04:96-114,140-188,219-243;
06:9-100,192-233,246-299; appendix A:28-84. No distribution or regret assertion
is made here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open CoordinatorPhaseClock

namespace Bandits.Support.ReferenceCompleteEmptyCollectionCorrectedChoiceDomains

variable {p : ConstructorDimensions.Parameters}

private theorem allFin_true {n : ℕ} (f : Fin n → Bool)
    (h : ∀ i, f i = true) : CoordinatorCollectionLedger.allFin n f = true := by
  simp only [CoordinatorCollectionLedger.allFin, List.all_eq_true]
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact h i

private theorem hazard_bounds (rate : ReferenceActivePhysicalStep.RateInput p) :
    0 < 4 * (p.m : ℝ) * rate.eta.val ∧
      0 ≤ 1 - 4 * (p.m : ℝ) * rate.eta.val := by
  have hm : (0 : ℝ) < p.m := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hKL : (1 : ℝ) ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast Nat.mul_le_mul
      (Nat.one_le_of_lt (ConstructorDimensions.K_pos p))
      (CanonicalRecordingRates.L_stab_ge_one p)
  have hden : 1024 * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      _ = (1024 * (p.m : ℝ)) * 1 := by ring
      _ ≤ (1024 * (p.m : ℝ)) *
          ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hKL (by positivity)
      _ = _ := by ring
  have heta : rate.eta.val ≤ 1 / (1024 * (p.m : ℝ)) :=
    rate.sourceCap.trans (one_div_le_one_div_of_le (by positivity) hden)
  have hprod : (p.m : ℝ) * rate.eta.val ≤ 1 / 1024 := by
    calc
      _ ≤ (p.m : ℝ) * (1 / (1024 * (p.m : ℝ))) :=
        mul_le_mul_of_nonneg_left heta hm.le
      _ = _ := by field_simp
  constructor
  · exact mul_pos (mul_pos (by norm_num) hm) rate.eta.property
  · nlinarith

private theorem corrected_mass_nonneg
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (l : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart l instruction)
    (hcutoff : l.cutoff ≤ instruction.time.val + 1)
    (hservice : ∀ a, (out.registers.cutoff a).lastService ≤
      (out.registers.cutoff a).score ∧
      (out.registers.cutoff a).lastService ≤ 4 * rate.n)
    (hincrement : ∀ a, l.increment a ≤
      4 * rate.n * (instruction.time.val + 1 - l.cutoff)) :
    ∀ S, 0 ≤ LaterAssignmentStartOperation.correctedRawMass old l instruction out
      (fun a => ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService))
      hcutoff S := by
  let h : ℝ := 4 * (p.m : ℝ) * rate.eta.val
  let ell := instruction.time.val + 1 - l.cutoff
  let c := out.registers.cutoff
  let b := AssignmentScoreReconstruction.sourceWeightBase p
  let wp := fun a => ScoreWeights.scoreWeight b ((c a).score - (c a).lastService)
  let wu := fun a => ScoreWeights.scoreWeight b (c a).score
  let wt := fun a => ScoreWeights.scoreWeight b ((c a).score + l.increment a)
  have hprev := (BoundedScoreProductDomination.bounded_score_product_domination rate
    (fun a => (c a).score - (c a).lastService) (fun a => (c a).lastService) 1
    (by intro a; simpa using (hservice a).2)).2
  have hnext := (BoundedScoreProductDomination.bounded_score_product_domination rate
    (fun a => (c a).score) l.increment ell hincrement).2
  have hcancel : ∀ a, (c a).score - (c a).lastService + (c a).lastService =
      (c a).score := fun a => Nat.sub_add_cancel (hservice a).1
  have hstep : ∀ S : PrefixSetSampler.SetCarrier p.K p.m,
      (1 - h) * LaterAssignmentStartOperation.productQOnPrefixCarrier wp S ≤
        LaterAssignmentStartOperation.productQOnPrefixCarrier wu S := by
    intro S
    simpa [LaterAssignmentStartOperation.productQOnPrefixCarrier, wp, wu, b, h,
      hcancel] using hprev (⟨S.1, S.2⟩ : ProductSetLaw.ProductSet p.K p.m)
  have hiter : ∀ S : PrefixSetSampler.SetCarrier p.K p.m,
      (1 - h) ^ ell * LaterAssignmentStartOperation.productQOnPrefixCarrier wu S ≤
        LaterAssignmentStartOperation.productQOnPrefixCarrier wt S := by
    intro S
    exact hnext ⟨S.1, S.2⟩
  obtain ⟨hhpos, hbase⟩ := hazard_bounds rate
  change 0 < h at hhpos
  change 0 ≤ 1 - h at hbase
  intro S
  let Qt := LaterAssignmentStartOperation.productQOnPrefixCarrier wt S
  let Qu := LaterAssignmentStartOperation.productQOnPrefixCarrier wu S
  let Qp := LaterAssignmentStartOperation.productQOnPrefixCarrier wp S
  have ht : 0 ≤ Qt - (1 - h) ^ ell * Qu := sub_nonneg.mpr (hiter S)
  have hu : 0 ≤ Qu - (1 - h) * Qp := sub_nonneg.mpr (hstep S)
  have hres : 0 ≤ (1 - h) ^ ell / h * (Qu - (1 - h) * Qp) :=
    mul_nonneg (div_nonneg (pow_nonneg hbase _) hhpos.le) hu
  have hid : Qt + (1 - h) ^ (ell + 1) / h * (Qu - Qp) =
      (Qt - (1 - h) ^ ell * Qu) +
        (1 - h) ^ ell / h * (Qu - (1 - h) * Qp) := by
    rw [pow_succ]
    field_simp
    ring
  change 0 ≤ Qt + (1 - h) ^ (ell + 1) / h * (Qu - Qp)
  rw [hid]
  exact add_nonneg ht hres

/-- The actual empty-pending corrected call has complete retained registers,
both reconstruction domain checks, all-arm service and increment bounds, the
old-anchor envelope, and normalized unclipped masses on every source vector.
Only the incoming source state, empty pending set, and strict old-boundary
comparison are conditional inputs. -/
theorem complete_empty_corrected_reconstruction
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ k : Fin R.length, let x := R[k.val].input
    ∀ (P : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      x.state.coordinator = .collection P l saved → l.pending = ∅ →
      x.time.val + 1 < l.freezeAt →
      ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
        let input := ReferenceActivePhysicalStep.collectionInput x P l
          (ReferenceActivePhysicalStep.collectionClock P l saved u) u
        ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
          (started : StartRoundResult p),
          startRound p rate.eta.val x.time input.clock l.pending = .ok started ∧
          ∃ instruction : AssignmentStartInstruction p,
            started.assignmentStart = some instruction ∧ instruction.time = x.time ∧
            instruction.kind = .corrected ∧
            let operation := CoordinatorRoundDispatch.collectionOperationLedger input
              core.payload_n_eq
            ∃ out : AssignmentScoreReconstruction.ReconstructedStart operation instruction,
              AssignmentScoreReconstruction.reconstructLaterStart operation instruction =
                .success operation instruction out ∧
              AssignmentScoreReconstruction.currentOutputDomainsCheck operation = true ∧
              AssignmentScoreReconstruction.previousOutputDomainsCheck operation instruction = true ∧
              ∃ hcutoff : operation.cutoff ≤ instruction.time.val + 1,
              (∀ a, (out.registers.cutoff a).lastService ≤ (out.registers.cutoff a).score ∧
                (out.registers.cutoff a).lastService ≤ 4 * rate.n) ∧
              (∀ a, operation.increment a ≤
                4 * rate.n * (instruction.time.val + 1 - operation.cutoff)) ∧
              (∀ a, P.anchor a ≤ AssignmentScoreReconstruction.currentWeight out a ∧
                AssignmentScoreReconstruction.currentWeight out a ≤ 2 * P.anchor a) ∧
              let previous := fun a => ScoreWeights.scoreWeight
                (AssignmentScoreReconstruction.sourceWeightBase p)
                ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService)
              AssignmentScoreReconstruction.previousWeight out = some previous ∧
              (∀ S, 0 ≤ LaterAssignmentStartOperation.correctedRawMass P operation instruction
                out previous hcutoff S) ∧
              (∑ S, LaterAssignmentStartOperation.correctedRawMass P operation instruction
                out previous hcutoff S) = 1 ∧
              (∀ vector : CheckedAssignmentSample.AssignmentVector p,
                ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
                  (LaterAssignmentStartOperation.correctedRawMass P operation instruction
                    out previous hcutoff) P.anchor vector = .sampled outcome) := by
  classical
  dsimp only
  intro k P l saved hstate hempty hbefore
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val].input
  have hstate' : x.state.coordinator = .collection P l saved := hstate
  obtain ⟨u, hu, core, _scores, started, hstart, _hnonempty, hassign⟩ :=
    ReferenceCompleteCollectionDispatchCore.complete_collection_dispatch_core
      rate rewards C_star C_h source k P l saved hstate
  obtain ⟨instruction, hinstruction, htime⟩ := hassign hempty
  let input := ReferenceActivePhysicalStep.collectionInput x P l
    (ReferenceActivePhysicalStep.collectionClock P l saved u) u
  let operation := CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
  have heffect := startRound_assignment_effect p rate.eta.val x.time input.clock l.pending
    started instruction core.clock_parameter_valid core.clock_registers_valid
    core.clock_start_time_valid hstart hinstruction
  have hkind : instruction.kind = .corrected := by
    have hk := heffect.2.1
    rw [core.clock_sigma_eq, ← core.ledger_freeze_eq] at hk
    change instruction.kind = (if l.freezeAt ≤ x.time.val + 1 then
      .renewal else .corrected) at hk
    exact hk.trans (ite_eq_right (Nat.not_le_of_lt
      (show x.time.val + 1 < l.freezeAt from hbefore)))
  have hv : CoordinatorCollectionLedger.validLedger operation := core.ledger_valid
  have hp : operation.phase = .ready := core.ledger_ready
  have hc : operation.cursor = instruction.time.val + 1 := by
    rw [htime]
    exact core.ledger_cursor_eq
  have he : operation.pending = ∅ := hempty
  have hk : instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
      operation.freezeAt instruction.time := by
    rw [hkind]
    symm
    apply (AssignmentScoreReconstruction.expectedLaterStartKind_eq_corrected_iff
      operation.freezeAt instruction.time).mpr
    simpa only [operation, CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput, htime] using hbefore
  let regs := AssignmentScoreReconstruction.extractCompleteRegisters operation hv he
  have hmass := (ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
    rate rewards C_star C_h source k).1
  unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hmass
  rw [hstate] at hmass
  have htimeBound : x.time.val * D p ≤ p.T * D p :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt x.time.isLt)
  have hbounds : ∀ a, (regs.cutoff a).score + operation.increment a ≤ p.T * D p ∧
      (regs.current a).queue ≤ p.T * D p := by
    intro a
    have hm := (hmass a (regs.cutoff a) (regs.current a)
      (regs.cutoff_eq a) (regs.current_eq a)).1
    have hm' : (regs.cutoff a).score + operation.increment a +
        (regs.current a).queue ≤ p.T * D p := hm.trans htimeBound
    omega
  have hcurrent : AssignmentScoreReconstruction.currentOutputDomainsCheck operation = true := by
    apply allFin_true
    intro a
    simp only [regs.cutoff_eq a, regs.current_eq a, decide_eq_true (hbounds a).1,
      decide_eq_true (hbounds a).2, Bool.and_self]
  have hservice :=
    ReferenceCompleteCollectionCutoffLastServiceBounds.complete_collection_input_cutoff_last_service_bound
      rate rewards C_star C_h source k P l saved hstate
  have hprevious : AssignmentScoreReconstruction.previousOutputDomainsCheck
      operation instruction = true := by
    unfold AssignmentScoreReconstruction.previousOutputDomainsCheck
    split
    · apply allFin_true
      intro a
      have hs := (hservice a (regs.cutoff a) (regs.cutoff_eq a)).1
      have hb : (regs.cutoff a).score - (regs.cutoff a).lastService ≤ p.T * D p := by
        have := (hbounds a).1
        omega
      simp only [regs.cutoff_eq a, dite_eq_left hs, decide_eq_true hb]
    · rfl
  have hex : ∃ out : AssignmentScoreReconstruction.ReconstructedStart operation instruction,
      AssignmentScoreReconstruction.reconstructLaterStart operation instruction =
        .success operation instruction out := by
    have hvcheck : CoordinatorCollectionLedger.validLedgerCheck operation = true := hv
    unfold AssignmentScoreReconstruction.reconstructLaterStart
    simp only [dite_eq_left hvcheck, dite_eq_left hp, dite_eq_left hc, dite_eq_left he, dite_eq_left hk,
      dite_eq_left hcurrent, dite_eq_left hprevious]
    exact ⟨_, rfl⟩
  obtain ⟨out, hout⟩ := hex
  have hspan := ReferenceCompleteCollectionIncrementSpan.complete_collection_input_increment_span
    rate rewards C_star C_h source k P l saved hstate
  dsimp only at hspan
  obtain ⟨_birth, _hprior, _hb, _hbase, _ha, _hs, _hu, _hg, _hpos,
    _hcf, _hterminal, hcutCursor, hcursor, hincrement⟩ := hspan
  have hcutoff : operation.cutoff ≤ instruction.time.val + 1 := by
    change l.cutoff ≤ instruction.time.val + 1
    rw [htime]
    omega
  have hsout : ∀ a, (out.registers.cutoff a).lastService ≤
      (out.registers.cutoff a).score ∧
      (out.registers.cutoff a).lastService ≤ 4 * rate.n := by
    intro a
    exact hservice a _ (out.registers.cutoff_eq a)
  have hiout : ∀ a, operation.increment a ≤
      4 * rate.n * (instruction.time.val + 1 - operation.cutoff) := by
    intro a
    have hi := hincrement a _ _ (out.registers.cutoff_eq a) (out.registers.current_eq a)
    have hmin : min l.cursor l.freezeAt = x.time.val + 1 := by
      rw [hcursor]
      exact min_eq_left (Nat.le_of_lt hbefore)
    rw [hmin] at hi
    simpa only [operation, CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput, htime] using hi
  have henv := ReferenceCompleteEpisodeScoreGrowth.complete_retained_episode_weight_envelopes
    p rate rewards C_star C_h source k
  rw [hstate] at henv
  have henvout : ∀ a, P.anchor a ≤ AssignmentScoreReconstruction.currentWeight out a ∧
      AssignmentScoreReconstruction.currentWeight out a ≤ 2 * P.anchor a := by
    intro a
    exact henv a _ _ (out.registers.cutoff_eq a) (out.registers.current_eq a)
  let previous := fun a => ScoreWeights.scoreWeight
    (AssignmentScoreReconstruction.sourceWeightBase p)
    ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService)
  have hprev : AssignmentScoreReconstruction.previousWeight out = some previous := by
    simp only [AssignmentScoreReconstruction.previousWeight,
      AssignmentScoreReconstruction.previousScore]
    have hbefore' : instruction.time.val + 1 < operation.freezeAt := by
      simpa only [operation, CoordinatorRoundDispatch.collectionOperationLedger, input,
        ReferenceActivePhysicalStep.collectionInput, htime] using hbefore
    simp only [ite_eq_left hbefore', Option.map_some]
    rfl
  have hn := corrected_mass_nonneg rate P operation instruction out hcutoff hsout hiout
  have hpos : ∀ a, 0 < AssignmentScoreReconstruction.currentWeight out a :=
    fun _ => ScoreWeights.scoreWeight_pos (AssignmentScoreReconstruction.sourceWeightBase_pos p) _
  have hcutpos : ∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight out a :=
    fun _ => ScoreWeights.scoreWeight_pos (AssignmentScoreReconstruction.sourceWeightBase_pos p) _
  have hprevpos : ∀ a, 0 < previous a :=
    fun _ => ScoreWeights.scoreWeight_pos (AssignmentScoreReconstruction.sourceWeightBase_pos p) _
  have hsum := LaterAssignmentStartOperation.correctedRawMass_sum_eq_one P operation
    instruction out previous hcutoff hpos hcutpos hprevpos
  refine ⟨u, hu, core, started, hstart, instruction, hinstruction, htime, hkind,
    out, hout, hcurrent, hprevious, hcutoff, hsout, hiout, henvout, hprev, hn, hsum, ?_⟩
  intro vector
  exact CheckedAssignmentSample.checkedAssignmentSample_normalized_success p
    ⟨_, hn, hsum⟩ P.anchor P.anchor_pos vector

private theorem later_success_of_corrected_sample
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (l : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old l)
    (out : AssignmentScoreReconstruction.ReconstructedStart l instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart l instruction =
      .success l instruction out)
    (hkind : instruction.kind = .corrected)
    (hcutoff : l.cutoff ≤ instruction.time.val + 1)
    (previous : Fin p.K → ℝ)
    (hprevious : AssignmentScoreReconstruction.previousWeight out = some previous)
    (hsample : ∀ vector : CheckedAssignmentSample.AssignmentVector p,
      ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
        (LaterAssignmentStartOperation.correctedRawMass old l instruction out previous hcutoff)
        old.anchor vector = .sampled outcome) :
    ∃ (output : LaterAssignmentStartOperation.SuccessfulStart old l instruction row)
      (hlocal : output.localConsistency = consistent),
      LaterAssignmentStartOperation.laterAssignmentStart old l instruction row consistent =
        .success output hlocal ∧ output.reconstruction = out := by
  classical
  have hpair :
      (⟨AssignmentScoreReconstruction.reconstructLaterStart l instruction, rfl⟩ :
        LaterAssignmentStartOperation.ReconstructionCall old l instruction) =
      ⟨.success l instruction out, hrec⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hrec
  have hdecision : LaterAssignmentStartOperation.decideReconstruction old l instruction =
      .success out hrec := by
    unfold LaterAssignmentStartOperation.decideReconstruction
    rw [hpair]
    rfl
  have hcurrentPos : ∀ a, 0 < AssignmentScoreReconstruction.currentWeight out a :=
    fun _ => ScoreWeights.scoreWeight_pos (AssignmentScoreReconstruction.sourceWeightBase_pos p) _
  have hcutoffPos : ∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight out a :=
    fun _ => ScoreWeights.scoreWeight_pos (AssignmentScoreReconstruction.sourceWeightBase_pos p) _
  let law := Classical.choose (LaterAssignmentStartOperation.selectLaw?_isSome
    old l instruction out hrec hcutoff hcurrentPos)
  have hlaw := Classical.choose_spec (LaterAssignmentStartOperation.selectLaw?_isSome
    old l instruction out hrec hcutoff hcurrentPos)
  change LaterAssignmentStartOperation.selectLaw? old l instruction out hcutoff hcurrentPos =
    some law at hlaw
  obtain ⟨prev, hprev, hanchor, hmass⟩ :=
    LaterAssignmentStartOperation.selectLaw?_corrected_spec old l instruction out
      hcutoff hcurrentPos law hlaw hkind
  have hprevEq : prev = previous := Option.some.inj (hprev.symm.trans hprevious)
  subst prev
  have hmassEq : law.mass =
      LaterAssignmentStartOperation.correctedRawMass old l instruction out previous hcutoff :=
    funext hmass
  obtain ⟨outcome, hsampleAt⟩ := hsample
    (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
  have hsampleLaw : CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
        .sampled outcome := by
    rw [hmassEq, hanchor]
    exact hsampleAt
  have hrun : LaterAssignmentStartOperation.laterAssignmentStart old l instruction row consistent =
      LaterAssignmentStartOperation.finishCheckedSample old l instruction row consistent out hrec
        hcutoff hcurrentPos hcutoffPos law hlaw := by
    unfold LaterAssignmentStartOperation.laterAssignmentStart
    rw [hdecision]
    rfl
  rw [hrun]
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split
  · rename_i arm reason hbad
    rw [hsampleLaw] at hbad
    contradiction
  · rename_i set hbad
    rw [hsampleLaw] at hbad
    contradiction
  · exact ⟨_, rfl, rfl, rfl⟩

private def dispatcherCollectionConsistency
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x) :
    LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) := {
  oldStart_eq := by
    simpa [CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRoundDispatch.collectionOperationLedger] using core.ledger_sigma_eq.symm
  oldAssignment_eq := by
    intro i
    simpa [CoordinatorRoundDispatch.collectionOperationLedger] using
      (core.assignment_eq i).symm
  oldFreezeAt := x.ledger.freezeAt
  oldFreezeAt_eq := by rfl }

private theorem dispatcherCollectionConsistency_eq
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)) :
    dispatcherCollectionConsistency x core = consistent := by
  cases consistent with
  | mk hstart hassignment oldFreeze hfreeze =>
      have hfreeze' : oldFreeze = x.ledger.freezeAt := by
        simpa [CoordinatorRoundDispatch.collectionOperationLedger] using hfreeze
      subst oldFreeze
      rfl

private theorem dispatchCollection_laterChosen
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq))
    (output : LaterAssignmentStartOperation.SuccessfulStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row)
    (hlocal : output.localConsistency = consistent)
    (htime : instruction.time = x.time)
    (hfreeze : x.clock.g = output.localConsistency.oldFreezeAt)
    (hpending : x.ledger.pending = ∅)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row consistent = .success output hlocal) :
    let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
      priorClock := x.clock
      pending := x.ledger.pending
      proposalParameterValid := core.clock_parameter_valid
      priorClockValid := core.clock_registers_valid
      startTimeValid := by rw [htime]; exact core.clock_start_time_valid
      result := started
      startRound_eq := by rw [htime]; exact hstart
      assignmentStart_eq := hassignment
      priorSigma_eq := core.clock_sigma_eq
      priorGrid_eq_freezeAt := hfreeze }
    let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
    (∀ i, installation.retainedBaseScore i ≤ p.T * ConstructorDimensions.D p) →
    CoordinatorLocalArmChoice.ChoiceInputsValid installation.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      instruction.time installation.registers.complementWeights →
    installation.registers.complementEnvelopeValid →
    ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
      started instruction.time installation.registers.complementWeights x.row,
      CoordinatorRoundDispatch.dispatchCollection x =
        .laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selection := by
  classical
  dsimp only
  intro hbase hchoice henvelope
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hnotpending : ¬ x.ledger.pending.Nonempty := by
    rw [hpending]
    simp
  have hconsistent := dispatcherCollectionConsistency_eq x core consistent
  cases hconsistent
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hactual
    rw [hstart] at hactual
    cases hactual
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hstart)
    subst actual
    simp [core, hnotpending]
    split
    · rename_i hmissing
      rw [hassignment] at hmissing
      cases hmissing
    · rename_i actualInstruction hactualInstruction
      have hi : actualInstruction = instruction :=
        Option.some.inj (hactualInstruction.symm.trans hassignment)
      subst actualInstruction
      simp only [dispatcherCollectionConsistency] at hlater
      split
      · rename_i actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualArm actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i set hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualOutput actualLocal hactualLater
        have heq := hactualLater.symm.trans hlater
        cases heq
        rw [ite_eq_left hbase]
        rw [dite_eq_left hchoice]
        rw [ite_eq_left henvelope]
        have hclockEquations := CoordinatorPhaseClock.startRound_assignment_effect p
          x.etaReal x.time x.clock x.ledger.pending started instruction
          core.clock_parameter_valid core.clock_registers_valid
          core.clock_start_time_valid hstart hassignment
        rcases hclockEquations with
          ⟨htimeActual, _, hnewSigma, _, _, _, _, _⟩
        have hgrid : CoordinatorPhaseClock.clockGridDomain p started.clock := by
          simpa [hnewSigma] using started.gridDomain
        have hgrid' := hgrid
        simp only [CoordinatorPhaseClock.clockGridDomain, hnewSigma] at hgrid'
        have hboundary : started.clock.g ≤ p.T + 1 := hgrid'.2
        have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          installation.registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          instruction.time installation.registers.complementWeights x.row hchoice
        split
        · rename_i hselected
          exact False.elim (hnonempty hselected)
        · rename_i arm hselected
          refine ⟨{
            arm := arm
            choiceInputsValid := hchoice
            recorderBoundaryValid := hboundary
            armChoice_eq := hselected }, ?_⟩
          rfl


/-- Every actual empty-pending collection call strictly before its old boundary
executes the corrected sampler successfully, installs that same output, and
selects an arm in the original physical PREPARE. All numerical checks and
old-anchor envelopes are produced internally from the complete source history.
This is a local feasibility and selection result, not a distribution law. -/
theorem complete_empty_corrected_choice_domains
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ k : Fin R.length, let x := R[k.val].input
    ∀ (P : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      x.state.coordinator = .collection P l saved → l.pending = ∅ →
      x.time.val + 1 < l.freezeAt →
      ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
        let clock := ReferenceActivePhysicalStep.collectionClock P l saved u
        let input := ReferenceActivePhysicalStep.collectionInput x P l clock u
        ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
          (started : StartRoundResult p)
          (hstart : startRound p rate.eta.val x.time input.clock l.pending = .ok started)
          (instruction : AssignmentStartInstruction p)
          (hassignment : started.assignmentStart = some instruction),
          instruction.time = x.time ∧ instruction.kind = .corrected ∧
          started.clock.sigma = some x.time ∧ started.clock.u = none ∧
          let operation := CoordinatorRoundDispatch.collectionOperationLedger input
            core.payload_n_eq
          ∃ (consistent : LaterAssignmentStartOperation.LocalConsistency P operation)
            (output : LaterAssignmentStartOperation.SuccessfulStart P operation instruction x.row)
            (hlocal : output.localConsistency = consistent),
            LaterAssignmentStartOperation.laterAssignmentStart P operation instruction x.row
              consistent = .success output hlocal ∧
            ∃ (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
              (installation : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
              (selected : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
                started instruction.time installation.registers.complementWeights x.row),
              clockData.priorClock = clock ∧ clockData.result = started ∧
              clockData.pending = l.pending ∧
              installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
              CoordinatorRoundDispatch.dispatchCollection input =
                .laterChosen core consistent started hstart instruction hassignment
                  output hlocal clockData installation selected ∧
              installation.registers.scoreDomainValid ∧
              installation.ownedRegisters.queueDomainValid ∧
              installation.ownedRegisters.previousServiceDomainValid ∧
              (∀ i, installation.retainedBaseScore i ≤ p.T * D p) ∧
              installation.registers.complementEnvelopeValid ∧
              installation.registers.payload = output.payload ∧
              output.payload.anchor = P.anchor ∧ output.law.anchor = P.anchor ∧
              (∀ a, l.cutoffRegisters a = some (output.reconstruction.registers.cutoff a)) ∧
              (∀ a, l.currentRegisters a = some (output.reconstruction.registers.current a)) ∧
              (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                (output.reconstruction.registers.cutoff a).score + l.increment a) ∧
              (∀ a, AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                (output.reconstruction.registers.current a).queue) ∧
              (∀ a, output.payload.queues a =
                (output.reconstruction.registers.current a).queue) ∧
              (∀ a, AssignmentScoreReconstruction.currentWeight output.reconstruction a =
                AssignmentScoreReconstruction.sourceWeightBase p ^
                  ((output.reconstruction.registers.cutoff a).score + l.increment a)) ∧
              (∀ a, AssignmentScoreReconstruction.cutoffWeight output.reconstruction a =
                AssignmentScoreReconstruction.sourceWeightBase p ^
                  (output.reconstruction.registers.cutoff a).score) ∧
              (∀ a, P.anchor a ≤ AssignmentScoreReconstruction.currentWeight
                  output.reconstruction a ∧
                AssignmentScoreReconstruction.currentWeight output.reconstruction a ≤
                  2 * P.anchor a) ∧
              let previous := fun a => ScoreWeights.scoreWeight
                (AssignmentScoreReconstruction.sourceWeightBase p)
                ((output.reconstruction.registers.cutoff a).score -
                  (output.reconstruction.registers.cutoff a).lastService)
              AssignmentScoreReconstruction.previousWeight output.reconstruction = some previous ∧
              (∀ S, output.law.mass S =
                LaterAssignmentStartOperation.productQOnPrefixCarrier
                  (AssignmentScoreReconstruction.currentWeight output.reconstruction) S +
                (1 - 4 * (p.m : ℝ) * rate.eta.val) ^
                    (x.time.val + 1 - l.cutoff + 1) / (4 * (p.m : ℝ) * rate.eta.val) *
                  (LaterAssignmentStartOperation.productQOnPrefixCarrier
                      (AssignmentScoreReconstruction.cutoffWeight output.reconstruction) S -
                    LaterAssignmentStartOperation.productQOnPrefixCarrier previous S)) ∧
              (∀ S, 0 ≤ output.law.mass S) ∧ (∑ S, output.law.mass S) = 1 ∧
              (∀ vector : CheckedAssignmentSample.AssignmentVector p,
                ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
                  output.law.mass P.anchor vector = .sampled outcome) ∧
              output.assignmentVector =
                LaterAssignmentStartOperation.ownAssignmentVector x.row x.time ∧
              ∃ v : ReferenceActivePhysicalStep.Selection x,
                (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some v ∧
                R[k.val].output.preparation.coordinator.selection = some v ∧
                v.view.payload = installation.registers.payload ∧
                v.started = started ∧ v.view.cutoff = none ∧ v.arm = selected.arm ∧
                CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff x.time := by
  classical
  dsimp only
  intro k P l saved hstate hempty hbefore
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let x := R[k.val].input
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
    out, hrec, _hcurrent, _hprevious, hcutoff, _hservice, _hincrement,
    henvelope, hprevious, hnonneg, hsum, hsample⟩ :=
    complete_empty_corrected_reconstruction rate rewards C_star C_h source k
      P l saved hstate hempty hbefore
  let clock := ReferenceActivePhysicalStep.collectionClock P l saved u
  have htimeX : instruction.time = x.time := htime
  let input := ReferenceActivePhysicalStep.collectionInput x P l clock u
  let operation := CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
  let consistent := dispatcherCollectionConsistency input core
  let previous := fun a => ScoreWeights.scoreWeight
    (AssignmentScoreReconstruction.sourceWeightBase p)
    ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService)
  obtain ⟨output, hlocal, hlater, hreconstruction⟩ :=
    later_success_of_corrected_sample rate P operation instruction x.row consistent
      out hrec hkind hcutoff previous hprevious hsample
  have hfreeze : input.clock.g = output.localConsistency.oldFreezeAt := by
    calc
      input.clock.g = input.ledger.freezeAt := core.ledger_freeze_eq.symm
      _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
      _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := input.clock
    pending := input.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hdomains := CoordinatorAssignmentRegisterInstall.later_register_domains output clockData
  have hbase : ∀ i, installation.retainedBaseScore i ≤ p.T * D p := by
    intro i
    change output.baseScore i ≤ p.T * D p
    exact (output.baseScore_eq_source i).trans_le
      (output.reconstruction.currentScore_le _)
  have hanchor : output.payload.anchor = P.anchor :=
    CoordinatorAssignmentRegisterInstall.later_payload_anchor_corrected output clockData hkind
  have henv : ∀ a, P.anchor a ≤
      AssignmentScoreReconstruction.currentWeight output.reconstruction a ∧
      AssignmentScoreReconstruction.currentWeight output.reconstruction a ≤ 2 * P.anchor a := by
    rw [hreconstruction]
    exact henvelope
  have hrecorder : installation.registers.complementEnvelopeValid := by
    intro j
    change output.payload.anchor j.1 ≤
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 ∧
      AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 ≤
        2 * output.payload.anchor j.1
    rw [hanchor]
    exact henv j.1
  have heffects := startRound_assignment_effect p rate.eta.val x.time input.clock l.pending
    started instruction core.clock_parameter_valid core.clock_registers_valid
    core.clock_start_time_valid hstart hassignment
  have hsigma := heffects.2.2.1
  have hnone := heffects.2.2.2.1
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid installation.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      instruction.time installation.registers.complementWeights := by
    apply CoordinatorLocalArmChoice.choiceInputsValid_mk
    · change output.payload.sigma.val + 1 ≤ instruction.time.val + 1
      rw [output.payload_start]
    · rw [hnone]
      change output.payload.sigma.val + 1 ≤ p.T + 1
      exact Nat.add_le_add_right (Nat.le_of_lt output.payload.sigma.isLt) 1
    · intro j
      exact ⟨installation.registers.complementWeights_pos j,
        (hrecorder j).1, (hrecorder j).2⟩
  obtain ⟨selected, hdispatch⟩ := dispatchCollection_laterChosen input core started hstart
    instruction hassignment consistent output hlocal htime hfreeze hempty hlater
    hbase hchoice hrecorder
  have hstate' : x.state.coordinator = .collection P l saved := hstate
  have hprepare : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection P l clock u (.laterChosen core consistent started hstart instruction
        hassignment output hlocal clockData installation selected) := by
    have hrange : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
      constructor <;> have := u.isLt <;> omega
    have hval : l.cutoff - 1 = u.val := by omega
    let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
    have hcut : cutoff = u := Fin.ext hval
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate', dite_eq_left hrange, CoordinatorRoundDispatch.dispatch]
    change ReferenceActivePhysicalStep.DispatchCut.collection P l
      (ReferenceActivePhysicalStep.collectionClock P l saved cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput x P l
          (ReferenceActivePhysicalStep.collectionClock P l saved cutoff) cutoff)) = _
    rw [hcut]
    exact congrArg (ReferenceActivePhysicalStep.DispatchCut.collection P l clock u) hdispatch
  let v : ReferenceActivePhysicalStep.Selection x := {
    view := {
      payload := installation.registers.payload
      pendingAtChoice := started.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
      complementWeights := installation.registers.complementWeights }
    started := started
    pending_eq := rfl
    cutoff_eq := rfl
    arm := selected.arm
    choice_eq := by
      have hselected : CoordinatorLocalArmChoice.coordinatorArmChoice
          installation.registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          instruction.time installation.registers.complementWeights x.row = some selected.arm :=
        selected.armChoice_eq
      simpa only [htimeX] using hselected }
  have hv : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some v := by
    rw [hprepare]
    change ReferenceActivePhysicalStep.selectionAt x installation.registers.payload started
      instruction.time installation.registers.complementWeights selected = some v
    simp only [ReferenceActivePhysicalStep.selectionAt, dite_eq_left htimeX]
    rfl
  have hvactual : R[k.val].output.preparation.coordinator.selection = some v := by
    have hp : R[k.val].output.preparation = ReferenceActivePhysicalStep.prepare x := by
      rw [R[k.val].output_eq]
      rfl
    rw [hp]
    exact hv
  have hvnone : v.view.cutoff = none := by
    change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u = none
    rw [hnone]
    rfl
  have hvlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      x.time := by
    rw [hvnone]
    change output.payload.sigma.val + 1 ≤ x.time.val + 1 ∧ x.time.val + 1 < p.T + 1
    rw [output.payload_start, htime]
    exact ⟨le_rfl, Nat.add_lt_add_right x.time.isLt 1⟩
  have hlawspec := LaterAssignmentStartOperation.selectLaw?_corrected_spec P operation
    instruction output.reconstruction output.cutoffReached output.currentWeight_pos
    output.law output.law_selected hkind
  obtain ⟨prev, hprev, hlawanchor, hlawmass⟩ := hlawspec
  have hprevOutput : AssignmentScoreReconstruction.previousWeight output.reconstruction =
      some previous := by rw [hreconstruction]; exact hprevious
  have hprevEq : prev = previous := Option.some.inj (hprev.symm.trans hprevOutput)
  subst prev
  have hlawEq : output.law.mass = LaterAssignmentStartOperation.correctedRawMass P operation
      instruction out previous hcutoff := by
    funext S
    rw [hlawmass S, hreconstruction]
  have hnonnegLaw : ∀ S, 0 ≤ output.law.mass S := by rw [hlawEq]; exact hnonneg
  have hsumLaw : (∑ S, output.law.mass S) = 1 := by rw [hlawEq]; exact hsum
  have hsampleLaw : ∀ vector : CheckedAssignmentSample.AssignmentVector p,
      ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
        output.law.mass P.anchor vector = .sampled outcome := by
    rw [hlawEq]
    exact hsample
  refine ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
    hsigma, hnone, consistent, output, hlocal, hlater, clockData, installation, selected,
    rfl, rfl, rfl, rfl, hdispatch, hdomains.1, hdomains.2.1, hdomains.2.2,
    hbase, hrecorder, rfl, hanchor, hlawanchor,
    output.reconstruction.registers.cutoff_eq, output.reconstruction.registers.current_eq,
    (fun _ => rfl), (fun _ => rfl), ?_, (fun _ => rfl), (fun _ => rfl), henv,
    ?_, ?_, hnonnegLaw, hsumLaw, hsampleLaw, ?_,
    v, hv, hvactual, rfl, rfl, hvnone, rfl, hvlive⟩
  · intro a
    exact output.payload_queues a
  · rw [hreconstruction]
    exact hprevious
  · intro S
    have hprevLiteral : (fun a => ScoreWeights.scoreWeight
        (AssignmentScoreReconstruction.sourceWeightBase p)
        ((output.reconstruction.registers.cutoff a).score -
          (output.reconstruction.registers.cutoff a).lastService)) = previous := by
      rw [hreconstruction]
    rw [hprevLiteral, hlawmass S]
    change _ = _ + _ * (_ - _)
    dsimp only [LaterAssignmentStartOperation.correctedRawMass,
      LaterAssignmentStartOperation.correctionScale]
    rw [htime]
    rfl
  · rw [output.assignmentVector_eq_row_projection, htime]

end Bandits.Support.ReferenceCompleteEmptyCollectionCorrectedChoiceDomains

end

end
