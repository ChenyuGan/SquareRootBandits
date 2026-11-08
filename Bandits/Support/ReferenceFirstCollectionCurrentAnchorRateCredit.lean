/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentReplayReconstruction

import Mathlib.Tactic

/-!
# The original first collection call's anchor and inverse-rate credit

Sources: `04_slow_fast_learner.tex:96-188,292-315`,
`06_interruptions.tex:355-426`, and `appendix_a_local_protocol.tex:28-64`
in `sources/zip4/manuscript/`.

The actual incoming payload retains the first launch's all-one anchor and
grid. Its start is identified through the same initialized collection stream.
Before that grid the complete numerical prefix has at most one episode's
length, so the stopped queue machine gives an all-arm weight envelope.
Renewal instead uses the actual reconstructed current weights, identified with
that same machine only on the strict-past retained event.

These are internal first-call statements. They assert no conditional law,
energy estimate, later-call invariant, coupling, or manuscript closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionCurrentAnchorRateCredit

open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceFirstCollectionStreamEmptyDispatch (ActualNextDispatch)
open ReferenceFirstCollectionCurrentRetainedGate (pastCells? G)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)

variable {p : ConstructorDimensions.Parameters}

private theorem selected_parameters_congr
    {eta : ReferencePrelaunchFollower.LearningRate}
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

/-- Parameter lookup identifies this dispatch's reconstruction, without
identifying independently chosen existential dispatch witnesses. -/
private theorem actual_dispatch_parameters
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcoord : r.input.state.coordinator = .collection old l saved)
    (hp : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta)
    (k : ActualNextDispatch r.input old l saved)
    (hliteral : k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
      (ReferenceActivePhysicalStep.collectionInput r.input old l
        (ReferenceActivePhysicalStep.collectionClock old l saved k.cutoffTime)
        k.cutoffTime) k.core.payload_n_eq) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters old
      k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess = theta := by
  classical
  have hcutValid : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    have he := k.cutoffTimeEq
    have ht := k.cutoffTime.isLt
    omega
  have hcutFin : (⟨l.cutoff - 1, by omega⟩ : Fin p.T) = k.cutoffTime := by
    apply Fin.ext
    have he := k.cutoffTimeEq
    change l.cutoff - 1 = k.cutoffTime.val
    omega
  let clock := ReferenceActivePhysicalStep.collectionClock old l saved k.cutoffTime
  let input := ReferenceActivePhysicalStep.collectionInput r.input old l clock k.cutoffTime
  have hinputParameters :
      ReferenceLaterAssignmentFibreStep.collectionParameters? input = some theta := by
    change ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta at hp
    unfold ReferenceLaterAssignmentFibreStep.parameters? at hp
    rw [hcoord] at hp
    simp only [dite_eq_left hcutValid, hcutFin] at hp
    exact hp
  have hcoreInput : CoordinatorRoundDispatch.CollectionCoreValid input := k.core
  have hoperation :
      CoordinatorRoundDispatch.collectionOperationLedger input k.core.payload_n_eq =
        k.operationLedger := hliteral.symm
  have hstartParameters := hinputParameters
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hstartParameters
  have hstartInput : CoordinatorPhaseClock.startRound p input.etaReal input.time
      input.clock input.ledger.pending = .ok k.started := k.startCheck
  rw [hstartInput] at hstartParameters
  have hselectedParameters :
      LaterAssignmentStartMeasurability.selectedSamplerParameters? old
        ⟨k.operationLedger, k.instruction, k.consistent⟩ = some theta := by
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
      have heq := selected_parameters_congr input.payload
        ⟨CoordinatorRoundDispatch.collectionOperationLedger input hcore.payload_n_eq,
          k.instruction, ReferenceLaterAssignmentFibreStep.collectionConsistency input hcore⟩
        ⟨k.operationLedger, k.instruction, k.consistent⟩ hoperationCore rfl
      exact heq.symm.trans hselectedActual
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
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match,
    hdecision] at hselectedParameters
  exact Option.some.inj hselectedParameters

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The payload's start is inherited from the original cutoff, through the
same finite stream and actual-record option equation. -/
private theorem original_payload_start (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t)
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hactual : actualRecord rate rewards C_star C_h t z = some r)
    (hcoord : r.input.state.coordinator = .collection old l saved) :
    old.sigma.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
  obtain ⟨_n, r', _theta, _hr, _ht, hactual', _hcall, _hrows, _hselected,
    _hrewards, _hearlier, _hdate, _hc, _hs, _hrecords, _hshort,
    f, _e, _houtcome, _hu, _hn, _hprevious, _hstate, hcoord',
    _hcutoff, _hcursor, _hempty, _hknown, _hservice, _hincrement,
    _k, _hliteral, _hkcut, _hktime⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
      rate rewards C_star C_h u t z hz
  have he : r' = r := Option.some.inj (hactual'.symm.trans hactual)
  subst r'
  have hpay := (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
    (hcoord.symm.trans hcoord')).1
  rw [hpay, f.stream.payloadMatchesCutoff]
  exact f.stream.cutoffContext.2.1

/-- The next grid is one-based and clipped at `T+1`. Strictly preceding it
bounds elapsed time even when the start is exactly divisible by the horizon. -/
private theorem elapsed_le_horizon (sigma : Fin p.T) (t : Fin p.T)
    (hbefore : t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val sigma) :
    t.val - sigma.val ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hdiv : (sigma.val + 1) % H + H * ((sigma.val + 1) / H) = sigma.val + 1 :=
    Nat.mod_add_div _ _
  have hraw : H * ((sigma.val + 1) / H + 1) ≤ sigma.val + 1 + H := by
    rw [Nat.mul_succ]
    omega
  have hmin : FollowerCutoffScan.gridBoundary p rate.eta.val sigma ≤
      H * ((sigma.val + 1) / H + 1) := Nat.min_le_right _ _
  change t.val - sigma.val ≤ H
  omega

/-- The all-arm band for the stopped zero-launch machine follows from its
actual length. The overflow-detecting update and disabled rounds are included. -/
private theorem zero_launch_weight_envelope
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hlen : L.length ≤ ReplayWeightStability.episodeHorizon rate.eta.val)
    (a : Fin p.K) :
    1 ≤ RecordedQueueRun.scoreWeight (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate) L) a ∧
      RecordedQueueRun.scoreWeight (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate) L) a < 2 := by
  have h := RecordedEpisodeStability.execute_source_weight_envelope
    (queueParameters rate) (RecordedQueueRun.initialState p.K) L a hlen
  have hzero : RecordedQueueRun.scoreWeight (queueParameters rate)
      (RecordedQueueRun.initialState p.K) a = 1 := by
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]
  change 1 ≤ RecordedQueueRun.scoreWeight (queueParameters rate)
      (RecordedQueueRun.execute (queueParameters rate) L
        (RecordedQueueRun.initialState p.K)) a ∧ _
  rw [hzero, mul_one] at h
  exact ⟨h.1, h.2.1⟩

/-- On the original retained first-call event, the SAME actual calendar
anchor bounds every arm of the SAME retained numerical prefix. Its canonical
inverse-rate sum therefore has the original manuscript constant `R`. -/
theorem G_anchor_rate_credit (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ G rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p),
      pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ∧
      actualRecord rate rewards C_star C_h t z = some r ∧ r.input.time = t ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      (∀ a : Fin p.K,
        0 < theta.2 a ∧
        theta.2 a ≤ RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ∧
        RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ≤ 2 * theta.2 a) ∧
      (∑ a : Fin p.K,
        ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight (queueParameters rate)
              (RecordedQueueRun.run (queueParameters rate) L)) a /
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a) ≤
        CanonicalRecordingRates.R p := by
  classical
  obtain ⟨L, _n, r, theta, old, l, saved, hL, hlen, _hr, ht, hactual,
    hcall, hcalendar, hcoord, _hempty, k, hliteral, _hkcut, hktime,
    _hunstopped, hstopped⟩ :=
    ReferenceFirstCollectionCurrentReplayReconstruction.G_reconstruction
      rate rewards C_star C_h u t z hz
  obtain ⟨_, _, _, _, _, hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hpair := actual_dispatch_parameters r theta old l saved hcoord hp k hliteral
  have hfreeze : k.operationLedger.freezeAt = l.freezeAt := by
    rw [hliteral]
    rfl
  have hband : ∀ a : Fin p.K,
      0 < theta.2 a ∧
      theta.2 a ≤ RecordedQueueRun.scoreWeight (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate) L) a ∧
      RecordedQueueRun.scoreWeight (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate) L) a ≤ 2 * theta.2 a := by
    by_cases hbefore : t.val + 1 < l.freezeAt
    · have hkind : k.instruction.kind = .corrected := by
        rw [k.expectedKind]
        apply (AssignmentScoreReconstruction.expectedLaterStartKind_eq_corrected_iff
          k.operationLedger.freezeAt k.instruction.time).mpr
        rw [hfreeze, hktime]
        exact hbefore
      obtain ⟨previous, hprevious, _hformula⟩ :=
        (AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
          k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess hkind).2.2.1
      have hcorrected := LaterAssignmentJointCodeMeasurability.selectedSamplerParameters_corrected
        old k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess
        hkind previous hprevious
      have hanchor : theta.2 = old.anchor :=
        (congrArg Prod.snd hpair).symm.trans (congrArg Prod.snd hcorrected)
      have hsigma := original_payload_start rate rewards C_star C_h
        u t z hz.1 r old l saved hactual hcoord
      have hlength : L.length ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
        rw [hlen, ← hsigma]
        apply elapsed_le_horizon rate old.sigma t
        rw [← k.freeze]
        exact hbefore
      intro a
      rw [hanchor, k.unitAnchor a]
      have ha := zero_launch_weight_envelope rate L hlength a
      exact ⟨zero_lt_one, ha.1, by simpa only [mul_one] using ha.2.le⟩
    · have hkind : k.instruction.kind = .renewal := by
        rw [k.expectedKind]
        apply (AssignmentScoreReconstruction.expectedLaterStartKind_eq_renewal_iff
          k.operationLedger.freezeAt k.instruction.time).mpr
        rw [hfreeze, hktime]
        omega
      have hrenewal := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
        old k.operationLedger k.instruction k.reconstructed k.reconstructionSuccess hkind
      have hanchor : theta.2 = AssignmentScoreReconstruction.currentWeight k.reconstructed :=
        (congrArg Prod.snd hpair).symm.trans hrenewal.1
      intro a
      have hweight := (hstopped a).2
      have hpos : 0 < RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a := by
        exact ScoreWeights.scoreWeight_pos
          (ScoreWeights.sourceBase_pos
            (Nat.cast_pos.mpr (queueParameters rate).D_pos)) _
      rw [hanchor, hweight]
      exact ⟨hpos, le_rfl, by linarith only [hpos]⟩
  refine ⟨L, r, theta, hL, hlen, hactual, ht, hcall, hcalendar, hband, ?_⟩
  exact CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    theta.2 (RecordedQueueRun.scoreWeight (queueParameters rate)
      (RecordedQueueRun.run (queueParameters rate) L))
    (fun a => (hband a).1) (fun a => (hband a).2)

/-- The same pointwise credit uses the literal rate vector of the actual
current cell. The selected physical payload has exactly the same calendar
anchor, including on the corrected branch. -/
theorem G_actual_rate_credit (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ G rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p)
      (selected : ReferenceActivePhysicalStep.Selection r.input)
      (c : RecordedQueueRun.RoundInput p.K),
      pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ∧
      actualRecord rate rewards C_star C_h t z = some r ∧ r.input.time = t ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload.anchor = theta.2 ∧
      c.rate = (fun a => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) ∧
      (∀ a : Fin p.K,
        0 < theta.2 a ∧
        theta.2 a ≤ RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ∧
        RecordedQueueRun.scoreWeight (queueParameters rate)
          (RecordedQueueRun.run (queueParameters rate) L) a ≤ 2 * theta.2 a) ∧
      (∑ a : Fin p.K,
        ProductSetLaw.theta p.m
            (RecordedQueueRun.scoreWeight (queueParameters rate)
              (RecordedQueueRun.run (queueParameters rate) L)) a / c.rate a) ≤
        CanonicalRecordingRates.R p := by
  classical
  obtain ⟨L, r, theta, hL, hlen, hactual, ht, hcall, hcalendar, hband, hsum⟩ :=
    G_anchor_rate_credit rate rewards C_star C_h u t z hz
  obtain ⟨_n, r', theta', selected, c, _hn, _ht', hactual', _hrows,
    _hselectedRow, _hrewards, hcalendar', hselected, _hchosen, hcell,
    hread, hanchor, _hpos⟩ :=
    ReferenceFirstCollectionCurrentRecordedCell.firstCell_selected
      rate rewards C_star C_h u t z hz.1
  have hr : r' = r := Option.some.inj (hactual'.symm.trans hactual)
  subst r'
  have htheta : theta' = theta := Option.some.inj (hcalendar'.symm.trans hcalendar)
  subst theta'
  obtain ⟨_henabled, selected', hselected', _hreward, hrate, _harrival⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r c hread
  have hs : selected' = selected := Option.some.inj (hselected'.symm.trans hselected)
  subst selected'
  have hxi : c.rate = (fun a => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
    funext a
    rw [hrate, selected.view.payload.rate_eq_canonical, hanchor]
  refine ⟨L, r, theta, selected, c, hL, hlen, hactual, ht, hcall, hcalendar,
    hcell, hselected, hanchor, hxi, hband, ?_⟩
  rw [hxi]
  exact hsum

end Bandits.Support.ReferenceFirstCollectionCurrentAnchorRateCredit
