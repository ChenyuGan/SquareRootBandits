/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCallStoredBounds
public import Bandits.Support.BoundedScoreProductDomination

import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Admissibility of the original first corrected collection call

The actual first prechoice invocation is taken from the complete original
physical suffix.  Its corrected branch uses the literal reconstructed law
and the stored physical cutoff registers.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstCollectionCallStoredBounds

namespace Bandits.Support.ReferenceFirstCollectionCorrectedCallAdmissibility

variable {p : ConstructorDimensions.Parameters}
variable {eta : ReferencePrelaunchFollower.LearningRate}

private theorem selectedSamplerParameters?_congr
    (old : AssignmentStartPayload.Input p eta)
    (x y : LaterAssignmentStartMeasurability.LocalStartInput old)
    (hledger : x.1 = y.1) (hinstruction : x.2.1 = y.2.1) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters? old x =
      LaterAssignmentStartMeasurability.selectedSamplerParameters? old y := by
  rcases x with ⟨ledgerX, instructionX, consistentX⟩
  rcases y with ⟨ledgerY, instructionY, consistentY⟩
  dsimp at hledger hinstruction
  subst ledgerY
  subst instructionY
  rfl

/-- The original first collection call has its actual stored-register
reconstruction.  On the same-episode branch its selected corrected law is
nonnegative, normalized, and succeeds on every original assignment vector.
The same actual dispatch also proves the first-call domain readout is present.
-/
theorem firstCell_corrected_parameters_admissible
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p)
      (old : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (c : Fin p.K → CoordinatorCollectionLedger.CutoffRegister),
      R[n]? = some r ∧ r.input.time = t ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      r.input.state.coordinator = .collection old l saved ∧
      l.cutoff = u.val + 1 ∧ l.cursor = t.val + 1 ∧ l.pending = ∅ ∧
      (∀ arm, l.cutoffRegisters arm = some (c arm)) ∧
      (∀ arm, (c arm).lastService ≤ (c arm).score ∧ (c arm).lastService ≤ 4 * rate.n) ∧
      ((t.val + 1 < l.freezeAt) →
        let b := AssignmentScoreReconstruction.sourceWeightBase p
        let h := 4 * (p.m : ℝ) * rate.eta.val
        let ell := t.val - u.val
        let wt := fun arm => ScoreWeights.scoreWeight b ((c arm).score + l.increment arm)
        let wu := fun arm => ScoreWeights.scoreWeight b (c arm).score
        let wp := fun arm => ScoreWeights.scoreWeight b ((c arm).score - (c arm).lastService)
        theta.2 = old.anchor ∧
        (∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
          theta.1 S0 = LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0 +
            (1 - h) ^ (ell + 1) / h *
              (LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0 -
                LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0)) ∧
        (∀ S0, 0 ≤ theta.1 S0) ∧
        (∑ S0 : PrefixSetSampler.SetCarrier p.K p.m, theta.1 S0) = 1 ∧
        (∀ arm, 0 < theta.2 arm) ∧
        (∀ vector : CheckedAssignmentSample.AssignmentVector p,
          ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
            theta.1 theta.2 vector = .sampled outcome)) ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
      (ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z).isSome = true := by
  classical
  dsimp only
  obtain ⟨n, r, theta, hr, ht, hactual, hcall, hrows, hselected, hrewards,
      _hearlier, _hntime, _hcross, _hspan, _hrecords, _hwindow,
      f, e, _hempty, _hcutoffStart, _hstreamLength, _hprevious,
      hstate, hcoord, hcut, hcursor, hpending, _hregisters,
      hstoredBounds, hincrement, k, hliteral, hkcut, hktime⟩ :=
    firstCell_stored_bounds rate rewards C_star C_h u t z hz
  obtain ⟨_, _, _, _, _, hparameters⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  let old := f.stream.payload
  let l := f.ledger
  let saved := f.stream.saved
  have hfreeze : k.operationLedger.freezeAt = l.freezeAt := by
    rw [hliteral]
    rfl
  have hoperationCutoff : k.operationLedger.cutoff = l.cutoff := by
    rw [hliteral]
    rfl
  have hoperationIncrement : k.operationLedger.increment = l.increment := by
    rw [hliteral]
    rfl
  have hoperationRegisters : k.operationLedger.cutoffRegisters = l.cutoffRegisters := by
    rw [hliteral]
    rfl
  have hcutL : l.cutoff = u.val + 1 := by simpa [l] using hcut
  have hcursorL : l.cursor = t.val + 1 := by simpa [l] using hcursor
  let c : Fin p.K → CoordinatorCollectionLedger.CutoffRegister :=
    k.reconstructed.registers.cutoff
  have hregister : ∀ arm, l.cutoffRegisters arm = some (c arm) := by
    intro arm
    have h := k.reconstructed.registers.cutoff_eq arm
    rw [hoperationRegisters] at h
    exact h
  have hstored : ∀ arm, (c arm).lastService ≤ (c arm).score ∧
      (c arm).lastService ≤ 4 * rate.n := by
    intro arm
    exact hstoredBounds arm (c arm) (hregister arm)
  have hcutFinValid : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    rw [hcutL]
    exact ⟨by omega, by omega⟩
  have hcutFin :
      (⟨l.cutoff - 1, by omega⟩ : Fin p.T) = k.cutoffTime := by
    apply Fin.ext
    have hk : k.cutoffTime.val + 1 = l.cutoff := k.cutoffTimeEq
    change l.cutoff - 1 = k.cutoffTime.val
    rw [hcutL]
    omega
  have hcutoffReached : k.operationLedger.cutoff ≤ k.instruction.time.val + 1 := by
    rw [hoperationCutoff, hcut, k.instructionTime]
    have horder := k.cutoffBeforeCursor
    rw [hcut, hcursor] at horder
    omega
  have hparameters' :
      ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta := by
    exact hparameters
  have hselectedParameters :
      LaterAssignmentStartMeasurability.selectedSamplerParameters? old
        ⟨k.operationLedger, k.instruction, k.consistent⟩ = some theta := by
    let clock := ReferenceActivePhysicalStep.collectionClock old l saved k.cutoffTime
    let input := ReferenceActivePhysicalStep.collectionInput r.input old l clock k.cutoffTime
    have hinputParameters :
        ReferenceLaterAssignmentFibreStep.collectionParameters? input = some theta := by
      have hp := hparameters'
      unfold ReferenceLaterAssignmentFibreStep.parameters? at hp
      rw [hcoord] at hp
      have hvalidF : 1 ≤ f.ledger.cutoff ∧ f.ledger.cutoff ≤ p.T := by
        simpa [l] using hcutFinValid
      have hcutFinF :
          (⟨f.ledger.cutoff - 1, by omega⟩ : Fin p.T) = k.cutoffTime := by
        simpa [l] using hcutFin
      simp only [dite_eq_left hvalidF, hcutFinF] at hp
      change ReferenceLaterAssignmentFibreStep.collectionParameters? input = some theta
      simpa [input, clock, old, l, saved] using hp
    have hcoreInput : CoordinatorRoundDispatch.CollectionCoreValid input := by
      simpa [input, clock, ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, old, l, saved] using k.core
    have hoperation :
        CoordinatorRoundDispatch.collectionOperationLedger input k.core.payload_n_eq =
          k.operationLedger := by
      rw [← hliteral]
    have hstartParameters := hinputParameters
    unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hstartParameters
    have hstartInput :
        CoordinatorPhaseClock.startRound p input.etaReal input.time input.clock
            input.ledger.pending = .ok k.started := by
      simpa [input, clock, ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, old, l, saved] using k.startCheck
    rw [hstartInput] at hstartParameters
    by_cases hcore : CoordinatorRoundDispatch.CollectionCoreValid input
    · simp [hcore] at hstartParameters
      simp only [k.assignmentStart] at hstartParameters
      have hselectedActual :
          LaterAssignmentStartMeasurability.selectedSamplerParameters? input.payload
            ⟨CoordinatorRoundDispatch.collectionOperationLedger input hcore.payload_n_eq,
              k.instruction, ReferenceLaterAssignmentFibreStep.collectionConsistency input hcore⟩ =
            some theta := hstartParameters.2
      have hoperationCore :
          CoordinatorRoundDispatch.collectionOperationLedger input hcore.payload_n_eq =
            k.operationLedger := by
        simpa using hoperation
      have hselectedEq :
          LaterAssignmentStartMeasurability.selectedSamplerParameters? input.payload
              ⟨CoordinatorRoundDispatch.collectionOperationLedger input hcore.payload_n_eq,
                k.instruction, ReferenceLaterAssignmentFibreStep.collectionConsistency input hcore⟩ =
            LaterAssignmentStartMeasurability.selectedSamplerParameters? input.payload
              ⟨k.operationLedger, k.instruction, k.consistent⟩ := by
        exact selectedSamplerParameters?_congr input.payload
          ⟨CoordinatorRoundDispatch.collectionOperationLedger input hcore.payload_n_eq,
            k.instruction, ReferenceLaterAssignmentFibreStep.collectionConsistency input hcore⟩
          ⟨k.operationLedger, k.instruction, k.consistent⟩ hoperationCore rfl
      have hselectedInput := hselectedEq.symm.trans hselectedActual
      change LaterAssignmentStartMeasurability.selectedSamplerParameters? old
        ⟨k.operationLedger, k.instruction, k.consistent⟩ = some theta
      simpa [input, clock, ReferenceActivePhysicalStep.collectionInput, old, l, saved]
        using hselectedInput
    · exact False.elim (hcore hcoreInput)
  have hdecision :
      LaterAssignmentStartOperation.decideReconstruction old k.operationLedger k.instruction =
        .success k.reconstructed k.reconstructionSuccess := by
    have hpair :
        (⟨AssignmentScoreReconstruction.reconstructLaterStart
            k.operationLedger k.instruction, rfl⟩ :
          LaterAssignmentStartOperation.ReconstructionCall old k.operationLedger k.instruction) =
        ⟨.success k.operationLedger k.instruction k.reconstructed,
          k.reconstructionSuccess⟩ := by
      apply LaterAssignmentStartOperation.ReconstructionCall.ext
      exact k.reconstructionSuccess
    unfold LaterAssignmentStartOperation.decideReconstruction
    rw [hpair]
    rfl
  have hselectedMatch :=
    LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match old
      ⟨k.operationLedger, k.instruction, k.consistent⟩
  rw [hselectedMatch, hdecision] at hselectedParameters
  have hparameterPair :
      LaterAssignmentStartMeasurability.selectedSamplerParameters old
          k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess = theta :=
    Option.some.inj hselectedParameters
  have hsameResult :
      (t.val + 1 < l.freezeAt) →
        theta.2 = old.anchor ∧
        (∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
          theta.1 S0 =
            LaterAssignmentStartOperation.productQOnPrefixCarrier
                (fun arm => ScoreWeights.scoreWeight
                  (AssignmentScoreReconstruction.sourceWeightBase p)
                  ((c arm).score + l.increment arm)) S0 +
              (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (t.val - u.val + 1) /
                  (4 * (p.m : ℝ) * rate.eta.val) *
                (LaterAssignmentStartOperation.productQOnPrefixCarrier
                    (fun arm => ScoreWeights.scoreWeight
                      (AssignmentScoreReconstruction.sourceWeightBase p) (c arm).score) S0 -
                  LaterAssignmentStartOperation.productQOnPrefixCarrier
                    (fun arm => ScoreWeights.scoreWeight
                      (AssignmentScoreReconstruction.sourceWeightBase p)
                      ((c arm).score - (c arm).lastService)) S0)) ∧
        (∀ S0, 0 ≤ theta.1 S0) ∧
        (∑ S0 : PrefixSetSampler.SetCarrier p.K p.m, theta.1 S0) = 1 ∧
        (∀ arm, 0 < theta.2 arm) ∧
        (∀ vector : CheckedAssignmentSample.AssignmentVector p,
          ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
            theta.1 theta.2 vector = .sampled outcome) := by
    intro hsame
    have hkindCorrected : k.instruction.kind = .corrected := by
      have hexp := AssignmentScoreReconstruction.expectedLaterStartKind_eq_corrected_iff
        (p := p) l.freezeAt t
      have hkind := k.expectedKind
      rw [hfreeze, hktime] at hkind
      exact hkind.trans (hexp.mpr hsame)
    let b := AssignmentScoreReconstruction.sourceWeightBase p
    let hazard := 4 * (p.m : ℝ) * rate.eta.val
    let ell := t.val - u.val
    let wt := fun arm : Fin p.K =>
      ScoreWeights.scoreWeight b ((c arm).score + l.increment arm)
    let wu := fun arm : Fin p.K => ScoreWeights.scoreWeight b (c arm).score
    let wp := fun arm : Fin p.K =>
      ScoreWeights.scoreWeight b ((c arm).score - (c arm).lastService)
    have hprevious :
        AssignmentScoreReconstruction.previousWeight k.reconstructed = some wp := by
      simp [AssignmentScoreReconstruction.previousWeight,
        AssignmentScoreReconstruction.previousScore, hfreeze, hktime,
        hsame, wp, b, c]
    have hbpos : 0 < b := AssignmentScoreReconstruction.sourceWeightBase_pos p
    have hcurrentPos : ∀ arm, 0 < AssignmentScoreReconstruction.currentWeight k.reconstructed arm := by
      intro arm
      exact ScoreWeights.scoreWeight_pos hbpos _
    have hcutoffPos : ∀ arm, 0 < AssignmentScoreReconstruction.cutoffWeight k.reconstructed arm := by
      intro arm
      exact ScoreWeights.scoreWeight_pos hbpos _
    have hpreviousPos : ∀ arm, 0 < wp arm := by
      intro arm
      exact ScoreWeights.scoreWeight_pos hbpos _
    have hcorrectedPair :=
      LaterAssignmentJointCodeMeasurability.selectedSamplerParameters_corrected
        old k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess
        hkindCorrected wp hprevious
    have hthetaPair :
        theta = (LaterAssignmentStartOperation.correctedRawMass old k.operationLedger
          k.instruction k.reconstructed wp hcutoffReached, old.anchor) :=
      hparameterPair.symm.trans hcorrectedPair
    have hcurrentEq :
        AssignmentScoreReconstruction.currentWeight k.reconstructed = wt := by
      funext arm
      simp [AssignmentScoreReconstruction.currentWeight,
        AssignmentScoreReconstruction.sourceScore, wt, b, c,
        hoperationIncrement]
    have hcutoffEq :
        AssignmentScoreReconstruction.cutoffWeight k.reconstructed = wu := by
      funext arm
      rfl
    have htimeSpan : min l.cursor l.freezeAt - l.cutoff = ell := by
      rw [hcursor]
      have hcursorBeforeFreeze : t.val + 1 < l.freezeAt := by omega
      rw [min_eq_left (Nat.le_of_lt hcursorBeforeFreeze), hcut]
      omega
    have hscale :
        LaterAssignmentStartOperation.correctionScale old k.operationLedger
            k.instruction hcutoffReached =
          (1 - hazard) ^ (ell + 1) / hazard := by
      unfold LaterAssignmentStartOperation.correctionScale
      rw [hktime, hoperationCutoff, hcutL]
      simp only [hazard, ell]
      congr 2
      omega
    have hgrowth : ∀ arm, l.increment arm ≤ 4 * rate.n * ell := by
      intro arm
      have hi := hincrement arm
      rw [htimeSpan] at hi
      exact hi
    have hprevGrowth : ∀ arm, (c arm).lastService ≤ 4 * rate.n * 1 := by
      intro arm
      have hi := (hstored arm).2
      omega
    let zprev : Fin p.K → ℕ := fun arm => (c arm).score - (c arm).lastService
    let gprev : Fin p.K → ℕ := fun arm => (c arm).lastService
    have hprevBound :=
      (BoundedScoreProductDomination.bounded_score_product_domination
        rate zprev gprev 1 hprevGrowth).2
    have hcurrentBound :=
      (BoundedScoreProductDomination.bounded_score_product_domination
        rate (fun arm => (c arm).score) l.increment ell hgrowth).2
    have hstepDom : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        (1 - hazard) *
            LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0 ≤
          LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0 := by
      intro S0
      have hmem : S0.1 ∈ ProductSetLaw.support p.K p.m := by
        exact S0.2
      let S' : ProductSetLaw.ProductSet p.K p.m := ⟨S0.1, hmem⟩
      have hh := hprevBound S'
      have hcancel : ∀ arm, zprev arm + gprev arm = (c arm).score := by
        intro arm
        exact Nat.sub_add_cancel (hstored arm).1
      simpa [hazard, zprev, gprev, wp, wu, b, S',
        LaterAssignmentStartOperation.productQOnPrefixCarrier, hcancel] using hh
    have hiterDom : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        (1 - hazard) ^ ell *
            LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0 ≤
          LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0 := by
      intro S0
      have hmem : S0.1 ∈ ProductSetLaw.support p.K p.m := by
        exact S0.2
      let S' : ProductSetLaw.ProductSet p.K p.m := ⟨S0.1, hmem⟩
      have hh := hcurrentBound S'
      simpa [hazard, wt, wu, b, S',
        LaterAssignmentStartOperation.productQOnPrefixCarrier] using hh
    have hhpos : 0 < hazard := by
      dsimp [hazard]
      exact mul_pos (mul_pos (by norm_num)
        (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))) rate.eta.property
    have hmKLnat : 1 ≤ p.K * CanonicalRecordingRates.L_stab p :=
      Nat.mul_le_mul (Nat.one_le_of_lt (ConstructorDimensions.K_pos p))
        (CanonicalRecordingRates.L_stab_ge_one p)
    have hmKL : (1 : ℝ) ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
      exact_mod_cast hmKLnat
    have hmpos : (0 : ℝ) < (p.m : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
    have hdenLower : 1024 * (p.m : ℝ) ≤
        1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
      calc
        1024 * (p.m : ℝ) = (1024 * (p.m : ℝ)) * 1 := by ring
        _ ≤ (1024 * (p.m : ℝ)) *
            ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
          mul_le_mul_of_nonneg_left hmKL (by positivity)
        _ = 1024 * (p.m : ℝ) * (p.K : ℝ) *
            (CanonicalRecordingRates.L_stab p : ℝ) := by ring
    have hetaSmall : rate.eta.val ≤ 1 / (1024 * (p.m : ℝ)) := by
      calc
        rate.eta.val ≤
            1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
              (CanonicalRecordingRates.L_stab p : ℝ)) := rate.sourceCap
        _ ≤ 1 / (1024 * (p.m : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hdenLower
    have hmEta : (p.m : ℝ) * rate.eta.val ≤ 1 / 1024 := by
      calc
        (p.m : ℝ) * rate.eta.val ≤
            (p.m : ℝ) * (1 / (1024 * (p.m : ℝ))) :=
          mul_le_mul_of_nonneg_left hetaSmall hmpos.le
        _ = 1 / 1024 := by field_simp [ne_of_gt hmpos]
    have hhle : hazard ≤ 1 := by
      calc
        hazard = 4 * ((p.m : ℝ) * rate.eta.val) := by dsimp [hazard]; ring
        _ ≤ 4 * (1 / 1024) := by gcongr
        _ ≤ 1 := by norm_num
    have hqtNonneg : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        0 ≤ LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0 := by
      intro S0
      change 0 ≤ ProductSetLaw.Q p.m wt ⟨S0.1, S0.2⟩
      exact (ProductSetLaw.Q_pos wt (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
        p.m_lt_K (fun arm => ScoreWeights.scoreWeight_pos hbpos _) _).le
    have hquNonneg : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        0 ≤ LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0 := by
      intro S0
      change 0 ≤ ProductSetLaw.Q p.m wu ⟨S0.1, S0.2⟩
      exact (ProductSetLaw.Q_pos wu (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
        p.m_lt_K (fun arm => ScoreWeights.scoreWeight_pos hbpos _) _).le
    have hqpNonneg : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        0 ≤ LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0 := by
      intro S0
      change 0 ≤ ProductSetLaw.Q p.m wp ⟨S0.1, S0.2⟩
      exact (ProductSetLaw.Q_pos wp (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
        p.m_lt_K (fun arm => ScoreWeights.scoreWeight_pos hbpos _) _).le
    have hqCurrentSum :=
      LaterAssignmentStartOperation.productQOnPrefixCarrier_sum_eq_one wt
        (fun arm => ScoreWeights.scoreWeight_pos hbpos _)
    have hqCutoffSum :=
      LaterAssignmentStartOperation.productQOnPrefixCarrier_sum_eq_one wu
        (fun arm => ScoreWeights.scoreWeight_pos hbpos _)
    have hqPreviousSum :=
      LaterAssignmentStartOperation.productQOnPrefixCarrier_sum_eq_one wp
        (fun arm => ScoreWeights.scoreWeight_pos hbpos _)
    have hmassNonneg : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        0 ≤ LaterAssignmentStartOperation.correctedRawMass old k.operationLedger
          k.instruction k.reconstructed wp hcutoffReached S0 := by
      intro S0
      let Qt := LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0
      let Qu := LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0
      let Qp := LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0
      have ha : 0 ≤ 1 - hazard := sub_nonneg.mpr hhle
      have hiterResidual : 0 ≤ Qt - (1 - hazard) ^ ell * Qu :=
        sub_nonneg.mpr (hiterDom S0)
      have hstepResidual : 0 ≤ Qu - (1 - hazard) * Qp :=
        sub_nonneg.mpr (hstepDom S0)
      have hcoeff : 0 ≤ (1 - hazard) ^ ell / hazard :=
        div_nonneg (pow_nonneg ha ell) hhpos.le
      have hcorrection :
          0 ≤ (1 - hazard) ^ ell / hazard * (Qu - (1 - hazard) * Qp) :=
        mul_nonneg hcoeff hstepResidual
      have hidentity :
          Qt + (1 - hazard) ^ (ell + 1) / hazard * (Qu - Qp) =
            (Qt - (1 - hazard) ^ ell * Qu) +
              (1 - hazard) ^ ell / hazard * (Qu - (1 - hazard) * Qp) := by
        field_simp [ne_of_gt hhpos]
        ring
      have hprevEq : wp = wp := rfl
      change 0 ≤ LaterAssignmentStartOperation.productQOnPrefixCarrier
          (AssignmentScoreReconstruction.currentWeight k.reconstructed) S0 +
        LaterAssignmentStartOperation.correctionScale old k.operationLedger
          k.instruction hcutoffReached *
          (LaterAssignmentStartOperation.productQOnPrefixCarrier
              (AssignmentScoreReconstruction.cutoffWeight k.reconstructed) S0 -
            LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0)
      have hcurrentQ := congrArg
        (fun w => LaterAssignmentStartOperation.productQOnPrefixCarrier w S0) hcurrentEq
      have hcutoffQ := congrArg
        (fun w => LaterAssignmentStartOperation.productQOnPrefixCarrier w S0) hcutoffEq
      rw [hcurrentQ, hcutoffQ, hscale]
      change 0 ≤ Qt + (1 - hazard) ^ (ell + 1) / hazard * (Qu - Qp)
      rw [hidentity]
      exact add_nonneg hiterResidual hcorrection
    have hmassSum :
        (∑ S0 : PrefixSetSampler.SetCarrier p.K p.m,
          LaterAssignmentStartOperation.correctedRawMass old k.operationLedger
            k.instruction k.reconstructed wp hcutoffReached S0) = 1 := by
      exact LaterAssignmentStartOperation.correctedRawMass_sum_eq_one old
        k.operationLedger k.instruction k.reconstructed wp hcutoffReached
        hcurrentPos hcutoffPos hpreviousPos
    have hthetaMass :
        theta.1 = LaterAssignmentStartOperation.correctedRawMass old k.operationLedger
          k.instruction k.reconstructed wp hcutoffReached := congrArg Prod.fst hthetaPair
    have hthetaAnchor : theta.2 = old.anchor := congrArg Prod.snd hthetaPair
    have hthetaNonneg : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        0 ≤ theta.1 S0 := by
      intro S0
      rw [hthetaMass]
      exact hmassNonneg S0
    have hthetaSum : (∑ S0 : PrefixSetSampler.SetCarrier p.K p.m, theta.1 S0) = 1 := by
      simpa [hthetaMass] using hmassSum
    have hthetaAnchorPos : ∀ arm, 0 < theta.2 arm := by
      rw [hthetaAnchor]
      exact old.anchor_pos
    let mass : PrefixSetSampler.NormalizedMass p.K p.m
        (Nat.le_of_lt p.m_lt_K) :=
      ⟨theta.1, hthetaNonneg, by simpa [PrefixMassPartition.totalMass] using hthetaSum⟩
    have hsample : ∀ vector : CheckedAssignmentSample.AssignmentVector p,
        ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p
          theta.1 theta.2 vector = .sampled outcome := by
      intro vector
      exact CheckedAssignmentSample.checkedAssignmentSample_normalized_success
        p mass theta.2 hthetaAnchorPos vector
    have hformula : ∀ S0 : PrefixSetSampler.SetCarrier p.K p.m,
        theta.1 S0 =
          LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0 +
            (1 - hazard) ^ (ell + 1) / hazard *
              (LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0 -
                LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0) := by
      intro S0
      rw [hthetaMass]
      unfold LaterAssignmentStartOperation.correctedRawMass
      have hcurrentQ := congrArg
        (fun w => LaterAssignmentStartOperation.productQOnPrefixCarrier w S0) hcurrentEq
      have hcutoffQ := congrArg
        (fun w => LaterAssignmentStartOperation.productQOnPrefixCarrier w S0) hcutoffEq
      change LaterAssignmentStartOperation.productQOnPrefixCarrier
          (AssignmentScoreReconstruction.currentWeight k.reconstructed) S0 +
        LaterAssignmentStartOperation.correctionScale old k.operationLedger
          k.instruction hcutoffReached *
          (LaterAssignmentStartOperation.productQOnPrefixCarrier
              (AssignmentScoreReconstruction.cutoffWeight k.reconstructed) S0 -
            LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0) = _
      calc
        _ = LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0 +
              LaterAssignmentStartOperation.correctionScale old k.operationLedger
                k.instruction hcutoffReached *
                (LaterAssignmentStartOperation.productQOnPrefixCarrier
                    (AssignmentScoreReconstruction.cutoffWeight k.reconstructed) S0 -
                  LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0) := by
            exact congrArg
              (fun q => q + LaterAssignmentStartOperation.correctionScale old
                k.operationLedger k.instruction hcutoffReached *
                (LaterAssignmentStartOperation.productQOnPrefixCarrier
                    (AssignmentScoreReconstruction.cutoffWeight k.reconstructed) S0 -
                  LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0)) hcurrentQ
        _ = LaterAssignmentStartOperation.productQOnPrefixCarrier wt S0 +
              (1 - hazard) ^ (ell + 1) / hazard *
                (LaterAssignmentStartOperation.productQOnPrefixCarrier wu S0 -
                  LaterAssignmentStartOperation.productQOnPrefixCarrier wp S0) := by
            rw [hcutoffQ, hscale]
    exact ⟨hthetaAnchor, hformula, hthetaNonneg, hthetaSum, hthetaAnchorPos, hsample⟩
  have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
    obtain ⟨cutoff, hcutoffFin, core, started, hstart, instruction, hassignment,
      consistent, htime, hkind, hprepared, hfailureIff, hcases⟩ := k.classification
    rcases hcases with hbad | ⟨out, hrec, hsuccess⟩
    · obtain ⟨arm, cutoffRegister, hregisterBad, hserviceBad, _, _⟩ := hbad
      exact False.elim ((Nat.not_lt_of_ge
        (hstoredBounds arm cutoffRegister hregisterBad).1) hserviceBad)
    · rcases hsuccess with hprefix | hsampled
      · obtain ⟨hcutoffReached', hcurrentPos', law, arm, reason, hcorrected',
          hselect, previous, hprevious', hpreviousPos', hanchor, hlawMass,
          hlater, hfailed, state, hready, hstepFailure, hrawStatePos, hratio,
          hdispatchFailure⟩ := hprefix
        have hbranchCorrected : instruction.kind = .corrected := hcorrected'
        have htimeT : instruction.time = t := htime.trans ht
        let classInput := ReferenceActivePhysicalStep.collectionInput r.input
          f.stream.payload f.ledger
          (ReferenceActivePhysicalStep.collectionClock f.stream.payload f.ledger
            f.stream.saved cutoff) cutoff
        let classOperation : LaterAssignmentStartOperation.LocalLedger f.stream.payload :=
          CoordinatorRoundDispatch.collectionOperationLedger classInput core.payload_n_eq
        have hclassFreeze : classOperation.freezeAt = l.freezeAt := by
          change f.ledger.freezeAt = f.ledger.freezeAt
          rfl
        have hsameBranch : t.val + 1 < l.freezeAt := by
          rw [← htimeT, ← hclassFreeze]
          have hkindCorrect :
              AssignmentScoreReconstruction.expectedLaterStartKind
                  classOperation.freezeAt instruction.time = .corrected :=
            hkind.symm.trans hbranchCorrected
          exact (AssignmentScoreReconstruction.expectedLaterStartKind_eq_corrected_iff
            (p := p) classOperation.freezeAt instruction.time).mp hkindCorrect
        have hgood := hsameResult hsameBranch
        obtain ⟨_, _, _, _, _, hsuccessAll⟩ := hgood
        obtain ⟨outcome, hsampleAt⟩ := hsuccessAll
          (LaterAssignmentStartOperation.ownAssignmentVector r.input.row instruction.time)
        have hphysical :=
          ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch r.input
        change ReferenceLaterAssignmentFibreStep.parameters? r.input =
          ReferenceLaterAssignmentFibreStep.dispatchParameters?
            (ReferenceActivePhysicalStep.prepare r.input).coordinator at hphysical
        rw [hprepared, hdispatchFailure] at hphysical
        simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
          ReferenceLaterAssignmentFibreStep.outcomeParameters?] at hphysical
        rw [hparameters'] at hphysical
        have hselectedClass :
            LaterAssignmentStartMeasurability.selectedSamplerParameters? f.stream.payload
              ⟨classOperation, instruction, consistent⟩ = some theta := hphysical.symm
        have hclassDecision :
            LaterAssignmentStartOperation.decideReconstruction f.stream.payload
              classOperation instruction = .success out hrec := by
          have hpair :
              (⟨AssignmentScoreReconstruction.reconstructLaterStart classOperation instruction,
                  rfl⟩ : LaterAssignmentStartOperation.ReconstructionCall f.stream.payload
                    classOperation instruction) = ⟨.success classOperation instruction out, hrec⟩ := by
            apply LaterAssignmentStartOperation.ReconstructionCall.ext
            exact hrec
          unfold LaterAssignmentStartOperation.decideReconstruction
          rw [hpair]
          rfl
        have hmatch :=
          LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match
            f.stream.payload ⟨classOperation, instruction, consistent⟩
        rw [hmatch, hclassDecision] at hselectedClass
        have hclassPair :
            LaterAssignmentStartMeasurability.selectedSamplerParameters f.stream.payload
                classOperation instruction out hrec = theta :=
          Option.some.inj hselectedClass
        have hclassCorrected :=
          LaterAssignmentJointCodeMeasurability.selectedSamplerParameters_corrected
            f.stream.payload classOperation instruction out hrec hcorrected'
            previous hprevious'
        have hlawPair : (law.mass, law.anchor) =
            LaterAssignmentStartMeasurability.selectedSamplerParameters f.stream.payload
              classOperation instruction out hrec := by
          apply Prod.ext
          · funext S0
            change law.mass S0 =
              (LaterAssignmentStartMeasurability.selectedSamplerParameters f.stream.payload
                classOperation instruction out hrec).1 S0
            rw [hlawMass S0]
            rw [congrArg Prod.fst hclassCorrected]
            rfl
          · exact hanchor.trans (congrArg Prod.snd hclassCorrected).symm
        have hLawTheta : (law.mass, law.anchor) = theta := hlawPair.trans hclassPair
        have hfailEq := hfailed
        change CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector r.input.row instruction.time) =
            .prefixFailure (some arm) reason at hfailEq
        have hLawMass := congrArg Prod.fst hLawTheta
        have hLawAnchor := congrArg Prod.snd hLawTheta
        have hLawMass' : law.mass = theta.1 := by simpa using hLawMass
        have hLawAnchor' : law.anchor = theta.2 := by simpa using hLawAnchor
        rw [hLawMass', hLawAnchor'] at hfailEq
        rw [hsampleAt] at hfailEq
        cases hfailEq
      · obtain ⟨output, hlocal, clockData, installation, selection,
          hinstall, hchoice, hreconstruction, hstartResult, hdispatch, _⟩ := hsampled
        simp [ReferenceCollectionPhaseHistory.laterChosen, hprepared, hdispatch]
  have hcurrent :
      (ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z).isSome = true :=
    (ReferenceFirstCollectionCurrentNumericalCell.currentCell_isSome_iff
      rate rewards C_star C_h u t z hz).2 ⟨r, hactual, hchosen⟩
  refine ⟨n, r, theta, old, l, saved, c, hr, ht, hactual, hcall, hrows,
    hselected, hrewards, hcoord, hcut, hcursor, hpending, hregister, hstored,
    ?_, hchosen, hcurrent⟩
  intro hsame
  exact hsameResult hsame

end Bandits.Support.ReferenceFirstCollectionCorrectedCallAdmissibility

end
