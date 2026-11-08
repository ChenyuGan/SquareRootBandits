/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchFollowerPreparationLocality

/-!
# Own-information locality of actual follower observation

This module proves equality of the existing full local code and whole next
follower storage from equal incoming own storage, accepted preparation
coordinates, literal observation reads, and own collision-filtered feedback.
Each side uses its own original source, including its own declared row.

The named later consumer is the actual complete-history own-local storage
induction: it must produce incoming storage equality from permissible local
history and prove coordinate provenance. This module does not establish that
induction or an unconditional local-information theorem.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:20-28`,
`sources/zip4/manuscript/07_public_setup.tex:28-34,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationPreparationMeasurability
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualInitializationStepMeasurability
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualPostlaunchStepMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.FollowerVaryingActivationMeasurability

namespace Bandits.Support.ActualPostlaunchFollowerObservationLocality

abbrev Parameters := ActualPostlaunchFollowerPreparationLocality.Parameters
abbrev RateInput := ActualPostlaunchFollowerPreparationLocality.RateInput

variable {p : Parameters} {rate : RateInput p}

abbrev PastProp (t : Fin p.T) :=
  {r : Fin p.T // r.val < t.val} → BootstrapPrivateRoundStreams.Scalar

abbrev ObservationCurrentCoordinates (t : Fin p.T) :=
  BootstrapPrivateRoundStreams.Scalar × BootstrapPrivateRoundStreams.Scalar ×
    BootstrapPrivateRoundStreams.Scalar × (Fin p.m → BootstrapPrivateRoundStreams.Scalar) ×
      AffineChannelLaw.Sample (ContinuousLearningRows.B p) × PastProp (p := p) t

abbrev ObservationSourceCoordinates (t : Fin p.T) :=
  Unit ⊕ ((Bool × Option (Fin (M p) →
    BootstrapPrivateRoundStreams.Scalar × Bool)) ⊕
      ObservationCurrentCoordinates (p := p) t)

/-- The actual operation's literal observation reads for this follower.
Bootstrap rows are retained only at this block's own private ID and time;
declared rows retain the current logging/service coordinates, DOWN sample,
and raw proposal scalars strictly before the current time. -/
def observationSourceCoordinates {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor) :
    ObservationSourceCoordinates (p := p)
      (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) := by
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
  let source := ActualPostlaunchFollowerMeasurability.localSource x
  match ActualPostlaunchFollowerMeasurability.localFollower x with
  | .bootstrap startup =>
      match startup.blockCase with
      | .inactive => exact Sum.inl ()
      | .active _ privateID _ registers =>
          exact Sum.inr (Sum.inl
            (ActualBootstrapObservationCode.sourceIDs p source privateID time,
              if registers.pending.isSome then none else
                some (fun candidate =>
                  ((((ActualBootstrapObservationCode.sourceRows p source candidate).2 time).1
                      ContinuousControlSlice.Label.slot),
                    (ActualBootstrapObservationCode.sourceRows p source candidate).1
                      privateID time))))
  | .declared rowIndex _ configuration =>
      match configuration with
      | .dagger => exact Sum.inl ()
      | .ordinary _ _ =>
          let row := ActualBootstrapObservationCode.sourceRows p source rowIndex
          let current := row.2 time
          let past : PastProp (p := p) time := fun r =>
            (row.2 r.1).1 ContinuousControlSlice.Label.prop
          let currentCoordinates : ObservationCurrentCoordinates (p := p) time :=
            (current.1 ContinuousControlSlice.Label.rec,
              (current.1 ContinuousControlSlice.Label.thin,
                (current.1 ContinuousControlSlice.Label.prop,
                  ((fun k : Fin p.m => current.1 (ContinuousControlSlice.Label.pilot k)),
                    (current.2 (0, i), past)))))
          exact Sum.inr (Sum.inr currentCoordinates)

private theorem declaredObservationCoordinates_eq_readFacts
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (rowIndex : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hlocal : ActualPostlaunchFollowerMeasurability.localFollower x =
      .declared rowIndex activation (.ordinary state memory))
    (hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hp : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x')
    (ho : observationSourceCoordinates (rate := rate) hcursor i x =
      observationSourceCoordinates (rate := rate) hcursor i x') :
    let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
    let row := ActualBootstrapObservationCode.sourceRows p
      (ActualPostlaunchFollowerMeasurability.localSource x) rowIndex
    let row' := ActualBootstrapObservationCode.sourceRows p
      (ActualPostlaunchFollowerMeasurability.localSource x') rowIndex
    PublicDiscreteDraws.slotDraw (row.2 time).1 =
        PublicDiscreteDraws.slotDraw (row'.2 time).1 ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 time).1 =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 time).1 ∧
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1 =
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time).1 ∧
      (∀ player : Fin p.m, PublicDiscreteDraws.pilotDraw (K_pos p) player
        (row.2 time).1 = PublicDiscreteDraws.pilotDraw (K_pos p) player
          (row'.2 time).1) ∧
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (row.2 time).1 =
        PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (row'.2 time).1 ∧
      (row.2 time).1 ContinuousControlSlice.Label.rec =
        (row'.2 time).1 ContinuousControlSlice.Label.rec ∧
      (row.2 time).1 ContinuousControlSlice.Label.thin =
        (row'.2 time).1 ContinuousControlSlice.Label.thin ∧
      (row.2 time).1 ContinuousControlSlice.Label.prop =
        (row'.2 time).1 ContinuousControlSlice.Label.prop ∧
      (row.2 time).2 (0, i) = (row'.2 time).2 (0, i) ∧
      (∀ j : Fin p.T, j.val < time.val →
        (row.2 j).1 ContinuousControlSlice.Label.prop =
          (row'.2 j).1 ContinuousControlSlice.Label.prop) := by
  classical
  have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
      .declared rowIndex activation (.ordinary state memory) := hf.symm.trans hlocal
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
  let row := ActualBootstrapObservationCode.sourceRows p
    (ActualPostlaunchFollowerMeasurability.localSource x) rowIndex
  let row' := ActualBootstrapObservationCode.sourceRows p
    (ActualPostlaunchFollowerMeasurability.localSource x') rowIndex
  let control := (row.2 time).1
  let control' := (row'.2 time).1
  let affine := (row.2 time).2
  let affine' := (row'.2 time).2
  let prepCoords : ActualPostlaunchFollowerPreparationLocality.PreparationCurrentCoordinates
      (p := p) :=
    (control ContinuousControlSlice.Label.slot,
      (control ContinuousControlSlice.Label.sel,
        ((fun k : Fin p.m => control (ContinuousControlSlice.Label.tuple k)),
          (control (ContinuousControlSlice.Label.pilot
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)), affine (1, i)))))
  let prepCoords' : ActualPostlaunchFollowerPreparationLocality.PreparationCurrentCoordinates
      (p := p) :=
    (control' ContinuousControlSlice.Label.slot,
      (control' ContinuousControlSlice.Label.sel,
        ((fun k : Fin p.m => control' (ContinuousControlSlice.Label.tuple k)),
          (control' (ContinuousControlSlice.Label.pilot
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)), affine' (1, i)))))
  have hprepCoord : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
      (rate := rate) hcursor i x = Sum.inr (Sum.inr (Sum.inr prepCoords)) := by
    unfold ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
    rw [hlocal]
  have hprepCoord' : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
      (rate := rate) hcursor i x' = Sum.inr (Sum.inr (Sum.inr prepCoords')) := by
    unfold ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
    rw [hlocal']
  have hprep : prepCoords = prepCoords' := by
    have h := hp
    rw [hprepCoord, hprepCoord'] at h
    exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h))
  let past : PastProp (p := p) time := fun r =>
    (row.2 r.1).1 ContinuousControlSlice.Label.prop
  let past' : PastProp (p := p) time := fun r =>
    (row'.2 r.1).1 ContinuousControlSlice.Label.prop
  let obsCoords : ObservationCurrentCoordinates (p := p) time :=
    (control ContinuousControlSlice.Label.rec,
      (control ContinuousControlSlice.Label.thin,
        (control ContinuousControlSlice.Label.prop,
          ((fun k : Fin p.m => control (ContinuousControlSlice.Label.pilot k)),
            (affine (0, i), past)))))
  let obsCoords' : ObservationCurrentCoordinates (p := p) time :=
    (control' ContinuousControlSlice.Label.rec,
      (control' ContinuousControlSlice.Label.thin,
        (control' ContinuousControlSlice.Label.prop,
          ((fun k : Fin p.m => control' (ContinuousControlSlice.Label.pilot k)),
            (affine' (0, i), past')))))
  have hobsCoord : observationSourceCoordinates (rate := rate) hcursor i x =
      Sum.inr (Sum.inr obsCoords) := by
    unfold observationSourceCoordinates
    rw [hlocal]
  have hobsCoord' : observationSourceCoordinates (rate := rate) hcursor i x' =
      Sum.inr (Sum.inr obsCoords') := by
    unfold observationSourceCoordinates
    rw [hlocal']
  have hobs : obsCoords = obsCoords' := by
    have h := ho
    rw [hobsCoord, hobsCoord'] at h
    exact Sum.inr.inj (Sum.inr.inj h)
  have hslotRaw : control ContinuousControlSlice.Label.slot =
      control' ContinuousControlSlice.Label.slot := by
    simpa [prepCoords, prepCoords'] using congrArg Prod.fst hprep
  have hselRaw : control ContinuousControlSlice.Label.sel =
      control' ContinuousControlSlice.Label.sel := by
    simpa [prepCoords, prepCoords'] using congrArg (fun z => z.2.1) hprep
  have htupleRaw : (fun k : Fin p.m => control (ContinuousControlSlice.Label.tuple k)) =
      (fun k : Fin p.m => control' (ContinuousControlSlice.Label.tuple k)) := by
    simpa [prepCoords, prepCoords'] using congrArg (fun z => z.2.2.1) hprep
  have hrecRaw : control ContinuousControlSlice.Label.rec =
      control' ContinuousControlSlice.Label.rec := by
    simpa [obsCoords, obsCoords'] using congrArg Prod.fst hobs
  have hthinRaw : control ContinuousControlSlice.Label.thin =
      control' ContinuousControlSlice.Label.thin := by
    simpa [obsCoords, obsCoords'] using congrArg (fun z => z.2.1) hobs
  have hpropRaw : control ContinuousControlSlice.Label.prop =
      control' ContinuousControlSlice.Label.prop := by
    simpa [obsCoords, obsCoords'] using congrArg (fun z => z.2.2.1) hobs
  have hpilotsRaw : (fun k : Fin p.m => control (ContinuousControlSlice.Label.pilot k)) =
      (fun k : Fin p.m => control' (ContinuousControlSlice.Label.pilot k)) := by
    simpa [obsCoords, obsCoords'] using congrArg (fun z => z.2.2.2.1) hobs
  have hsampleRaw : affine (0, i) = affine' (0, i) := by
    simpa [obsCoords, obsCoords'] using congrArg (fun z => z.2.2.2.2.1) hobs
  have hpastRaw : past = past' := by
    simpa [obsCoords, obsCoords'] using congrArg (fun z => z.2.2.2.2.2) hobs
  have hslot : PublicDiscreteDraws.slotDraw control = PublicDiscreteDraws.slotDraw control' := by
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hslotRaw]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control' := by
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hselRaw]
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K control =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K control' :=
    OrderedTupleSampler.sample_eq_of_tupleInputs_eq p.two_le_m p.m_lt_K
      (fun k => congrFun htupleRaw k)
  have hpilots (player : Fin p.m) :
      PublicDiscreteDraws.pilotDraw (K_pos p) player control =
        PublicDiscreteDraws.pilotDraw (K_pos p) player control' := by
    unfold PublicDiscreteDraws.pilotDraw ContinuousControlSlice.coordinate
    rw [congrFun hpilotsRaw player]
  have hslot' : PublicDiscreteDraws.slotDraw (row.2 time).1 =
      PublicDiscreteDraws.slotDraw (row'.2 time).1 := by
    simpa [control, control'] using hslot
  have hselected' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 time).1 := by
    simpa [control, control'] using hselected
  have htuple' : OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time).1 := by
    simpa [control, control'] using htuple
  have hpilots' (player : Fin p.m) :
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 time).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 time).1 := by
    simpa [control, control'] using hpilots player
  have hsource : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K control =
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K control' := by
    unfold PublicDiscreteDraws.recorderSourceDraw ContinuousControlSlice.coordinate
    rw [hrecRaw]
  have hsource' : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (row'.2 time).1 := by
    simpa [control, control'] using hsource
  have hpast (j : Fin p.T) (hj : j.val < time.val) :
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (row'.2 j).1 ContinuousControlSlice.Label.prop := by
    have h := congrFun hpastRaw ⟨j, hj⟩
    simpa [past, past', row, row'] using h
  refine ⟨hslot', hselected', htuple', hpilots', hsource', ?_, ?_, ?_, ?_, hpast⟩
  · simpa [control, control'] using hrecRaw
  · simpa [control, control'] using hthinRaw
  · simpa [control, control'] using hpropRaw
  · simpa [affine, affine', row, row'] using hsampleRaw

private theorem recordOrServiceThenDownCode_eq_of_local_reads
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (values : FollowerDownMeasurability.SavedScalarFamily state.buffer.length)
    (hslot : PublicDiscreteDraws.slotDraw (row.2 time).1 =
      PublicDiscreteDraws.slotDraw (row'.2 time).1)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 time).1)
    (hsource : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (row'.2 time).1)
    (hpilots : ∀ player : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 time).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 time).1)
    (hsample : (row.2 time).2 (0, i) = (row'.2 time).2 (0, i))
    (hprop : ∀ j : Fin p.T, j.val < time.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (row'.2 j).1 ContinuousControlSlice.Label.prop) :
    FollowerLoggingDownMeasurability.recordOrServiceThenDownCode i rate activation
      state hstatus
        ((((row, ⟨time, hactive⟩), (feedback, arm)), values)) =
    FollowerLoggingDownMeasurability.recordOrServiceThenDownCode i rate activation
      state hstatus
        ((((row', ⟨time, hactive⟩), (feedback, arm)), values)) := by
  classical
  have hlogging :
      SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row activation time
            (arm, FollowerDownMeasurability.feedbackAtGrid p feedback)) =
        SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row' activation time
            (arm, FollowerDownMeasurability.feedbackAtGrid p feedback)) := by
    apply propext
    rw [ActiveFollowerLogging.loggingTestsPass_iff_source_mask,
      ActiveFollowerLogging.loggingTestsPass_iff_source_mask]
    simp [hslot, hsource, hpilots]
  have hselectedProp : ActiveFollowerDownAcceptance.downSelected p i row time =
      ActiveFollowerDownAcceptance.downSelected p i row' time := by
    apply propext
    simp [ActiveFollowerDownAcceptance.downSelected, hslot, hselected]
  have hcurrent : ActiveFollowerDownAcceptance.currentRoundInput p i row time
      (FollowerDownMeasurability.feedbackAtGrid p feedback) rate
      (FollowerDownMeasurability.adaptedInputState rate state values) =
    ActiveFollowerDownAcceptance.currentRoundInput p i row' time
      (FollowerDownMeasurability.feedbackAtGrid p feedback) rate
      (FollowerDownMeasurability.adaptedInputState rate state values) := by
    unfold ActiveFollowerDownAcceptance.currentRoundInput
    simp [hslot, hselected, hsample]
  have hpastBits : ∀ j : Fin p.T, j.val < time.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j =
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row' j := by
    intro j hj
    change FollowerCutoffScan.thresholdProposalBit
        ((row.2 j).1 ContinuousControlSlice.Label.prop)
        (FollowerCutoffScan.proposalHazard p rate.eta.val) =
      FollowerCutoffScan.thresholdProposalBit
        ((row'.2 j).1 ContinuousControlSlice.Label.prop)
        (FollowerCutoffScan.proposalHazard p rate.eta.val)
    rw [hprop j hj]
  have hdown := FollowerDownJointMeasurability.downTransitionCode_eq_of_currentInput_and_pastProposalBits
    i row row' time feedback rate state values hcurrent hpastBits
  have hfresh : FollowerLoggingDownMeasurability.currentKeyFresh
        ((((row, ⟨time, hactive⟩), (feedback, arm)), values)) =
      FollowerLoggingDownMeasurability.currentKeyFresh
        ((((row', ⟨time, hactive⟩), (feedback, arm)), values)) := by
    apply propext
    simp [FollowerLoggingDownMeasurability.currentKeyFresh,
      FollowerLoggingDownMeasurability.inputTime,
      FollowerLoggingDownMeasurability.inputPlayedArm]
  unfold FollowerLoggingDownMeasurability.recordOrServiceThenDownCode
  simp only [FollowerLoggingDownMeasurability.inputSavedScalars,
    FollowerLoggingDownMeasurability.inputRow, FollowerLoggingDownMeasurability.inputTime,
    FollowerLoggingDownMeasurability.inputPlayedArm,
    FollowerLoggingDownMeasurability.inputFeedbackIndex]
  simp only [hlogging, hselectedProp, hdown, hfresh]
  rfl

private theorem checkedServiceCodeAtJoint_eq_of_local_reads
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1))
    (values : FollowerDownMeasurability.SavedScalarFamily state.buffer.length)
    (hslot : PublicDiscreteDraws.slotDraw (row.2 time).1 =
      PublicDiscreteDraws.slotDraw (row'.2 time).1)
    (hsource : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (row'.2 time).1)
    (hpilots : ∀ player : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 time).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 time).1)
    (hthin : (row.2 time).1 ContinuousControlSlice.Label.thin =
      (row'.2 time).1 ContinuousControlSlice.Label.thin) :
    FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation state
      ((((row, time), feedback), values)) =
    FollowerServiceMeasurability.checkedServiceCodeAtJoint rate i activation state
      ((((row', time), feedback), values)) := by
  classical
  have hgate (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
      FollowerServiceMeasurability.recorderGateBit rate.eta i row time M =
        FollowerServiceMeasurability.recorderGateBit rate.eta i row' time M := by
    have hpred : ActiveFollowerQueueOperation.recorderGate rate.eta i row time M ↔
        ActiveFollowerQueueOperation.recorderGate rate.eta i row' time M := by
      unfold ActiveFollowerQueueOperation.recorderGate
      simp [CanonicalRecordingSlice.recordingMask,
        ContinuousControlSlice.coordinate, hslot, hsource, hthin, hpilots]
    have heq : ActiveFollowerQueueOperation.recorderGate rate.eta i row time M =
        ActiveFollowerQueueOperation.recorderGate rate.eta i row' time M := propext hpred
    unfold FollowerServiceMeasurability.recorderGateBit
    rw [heq]
  have hread : FollowerServiceMeasurability.serviceReadForState rate i state
      ((((row, time), feedback), values)) =
    FollowerServiceMeasurability.serviceReadForState rate i state
      ((((row', time), feedback), values)) := by
    cases hlast : state.lastDown with
    | none =>
        simp [FollowerServiceMeasurability.serviceReadForState,
          FollowerDownJointMeasurability.jointTime,
          FollowerDownJointMeasurability.jointRowTime,
          FollowerDownJointMeasurability.jointFeedbackIndex, hlast]
    | some M =>
        have hgateM := hgate M
        simp [FollowerServiceMeasurability.serviceReadForState,
          FollowerServiceMeasurability.recorderReadForDownAt,
          FollowerDownJointMeasurability.jointRow,
          FollowerDownJointMeasurability.jointRowTime,
          FollowerDownJointMeasurability.jointTime,
          FollowerDownJointMeasurability.jointFeedbackIndex, hlast, hgateM]
  rw [FollowerServiceMeasurability.checkedServiceCodeAtJoint_eq_readFactor,
    FollowerServiceMeasurability.checkedServiceCodeAtJoint_eq_readFactor]
  exact congrArg (FollowerServiceMeasurability.serviceCodeFromRead rate i activation state)
    hread

private theorem releaseAndFinishCodeAt_eq_of_local_reads
    (i : Fin (p.m - 1))
    (preChoice postService : FollowerReleaseFinishJointMeasurability.CarriedState p rate)
    (memory : FollowerReleaseFinishJointMeasurability.LocalMemoryCode p)
    (row row' : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (feedback : Fin (D p + 1))
    (hslot : PublicDiscreteDraws.slotDraw (row.2 time).1 =
      PublicDiscreteDraws.slotDraw (row'.2 time).1)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 time).1)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time).1)
    (hpilots : ∀ player : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 time).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 time).1)
    (hprop : (row.2 time).1 ContinuousControlSlice.Label.prop =
      (row'.2 time).1 ContinuousControlSlice.Label.prop) :
    FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
      rate i preChoice postService memory row time feedback =
    FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
      rate i preChoice postService memory row' time feedback := by
  have hpublic : ActiveFollowerLifecycle.publicRowOfCompleteRow row time =
      ActiveFollowerLifecycle.publicRowOfCompleteRow row' time := by
    unfold ActiveFollowerLifecycle.publicRowOfCompleteRow
    simp only [ActiveFollowerLifecycle.FollowerPublicRow.mk.injEq]
    exact ⟨hslot, hselected, htuple, funext hpilots⟩
  have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val row time =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row' time := by
    change FollowerCutoffScan.thresholdProposalBit
        ((row.2 time).1 ContinuousControlSlice.Label.prop)
        (FollowerCutoffScan.proposalHazard p rate.eta.val) =
      FollowerCutoffScan.thresholdProposalBit
        ((row'.2 time).1 ContinuousControlSlice.Label.prop)
        (FollowerCutoffScan.proposalHazard p rate.eta.val)
    rw [hprop]
  have hoperation : DeclaredFollowerLocalRound.releaseAndFinish rate i row time
      (FollowerDownMeasurability.feedbackAtGrid p feedback)
      (FollowerDownMeasurability.followerStateOfCode rate preChoice.1.1
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
          preChoice.1.2.2 preChoice.2))
      (FollowerLifecycleMeasurability.localMemoryOfCode memory)
      (FollowerDownMeasurability.followerStateOfCode rate postService.1.1
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
          postService.1.2.2 postService.2)) =
    DeclaredFollowerLocalRound.releaseAndFinish rate i row' time
      (FollowerDownMeasurability.feedbackAtGrid p feedback)
      (FollowerDownMeasurability.followerStateOfCode rate preChoice.1.1
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
          preChoice.1.2.2 preChoice.2))
      (FollowerLifecycleMeasurability.localMemoryOfCode memory)
      (FollowerDownMeasurability.followerStateOfCode rate postService.1.1
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
          postService.1.2.2 postService.2)) := by
    unfold DeclaredFollowerLocalRound.releaseAndFinish
    rw [hpublic]
    cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row' time)
        (FollowerDownMeasurability.feedbackAtGrid p feedback)
        (FollowerDownMeasurability.followerStateOfCode rate preChoice.1.1
          (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
            preChoice.1.2.2 preChoice.2))
        (FollowerDownMeasurability.followerStateOfCode rate postService.1.1
          (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
            postService.1.2.2 postService.2)) with
    | error reason => simp
    | ok afterRelease =>
        simp only
        have hfinish : ActiveFollowerLifecycle.finishRound rate.eta time row afterRelease
              (FollowerLifecycleMeasurability.localMemoryOfCode memory) =
            ActiveFollowerLifecycle.finishRound rate.eta time row' afterRelease
              (FollowerLifecycleMeasurability.localMemoryOfCode memory) := by
          unfold ActiveFollowerLifecycle.finishRound
          rw [hbit]
        rw [hfinish]
  unfold FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents
    FollowerLifecycleMeasurability.releaseAndFinishResultCodeAt
  rw [hoperation]

private theorem observationResultCode_eq_of_local_reads
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (carry : DeclaredFollowerObservationMeasurability.CarriedState p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : DeclaredFollowerObservationMeasurability.FollowerActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (hslot : PublicDiscreteDraws.slotDraw (row.2 time.1).1 =
      PublicDiscreteDraws.slotDraw (row'.2 time.1).1)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 time.1).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 time.1).1)
    (hpilots : ∀ player : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 time.1).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 time.1).1)
    (hsource : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      (row.2 time.1).1 = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (row'.2 time.1).1)
    (hthin : (row.2 time.1).1 ContinuousControlSlice.Label.thin =
      (row'.2 time.1).1 ContinuousControlSlice.Label.thin)
    (hsample : (row.2 time.1).2 (0, i) = (row'.2 time.1).2 (0, i))
    (hpast : ∀ j : Fin p.T, j.val < time.1.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (row'.2 j).1 ContinuousControlSlice.Label.prop) :
    FollowerObservationStageMeasurabilityRepair.observationResultCode rate i activation
      (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row time feedback arm) =
    FollowerObservationStageMeasurabilityRepair.observationResultCode rate i activation
      (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
        carry row' time feedback arm) := by
  classical
  let index := carry.1
  let values := carry.2
  let state := FollowerObservationStageMeasurabilityRepair.representativeState rate index
  let saved := FollowerObservationStageMeasurabilityRepair.representativeValues index values
  change FollowerObservationStageMeasurabilityRepair.observationResultCodeOnFiber
      rate i activation index
      (values, (((row, time), feedback), arm)) =
    FollowerObservationStageMeasurabilityRepair.observationResultCodeOnFiber
      rate i activation index
      (values, (((row', time), feedback), arm))
  unfold FollowerObservationStageMeasurabilityRepair.observationResultCodeOnFiber
  by_cases hstatus : state.status = .unoccupied
  · simp only [state, dite_eq_left hstatus]
    have hcode := recordOrServiceThenDownCode_eq_of_local_reads
      (rate := rate) i activation state hstatus row row' time.1 time.2
      feedback arm saved hslot hselected hsource hpilots hsample hpast
    simpa [FollowerObservationStageMeasurabilityRepair.loggingInputOfFiber,
      FollowerObservationStageMeasurabilityRepair.fiberRow,
      FollowerObservationStageMeasurabilityRepair.fiberTime,
      FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex,
      FollowerObservationStageMeasurabilityRepair.fiberPlayedArm,
      FollowerObservationStageMeasurabilityRepair.fiberValues,
      FollowerObservationStageMeasurabilityRepair.representativeValues,
      index, values, saved, state] using congrArg
        FollowerObservationStageMeasurabilityRepair.ObservationResultCode.unoccupied hcode
  · simp only [state, dite_eq_right hstatus]
    have hcode := checkedServiceCodeAtJoint_eq_of_local_reads
      (rate := rate) i activation state row row' time.1 feedback saved
      hslot hsource hpilots hthin
    simpa [FollowerObservationStageMeasurabilityRepair.serviceInputOfFiber,
      FollowerObservationStageMeasurabilityRepair.fiberRow,
      FollowerObservationStageMeasurabilityRepair.fiberTime,
      FollowerObservationStageMeasurabilityRepair.fiberFeedbackIndex,
      FollowerObservationStageMeasurabilityRepair.fiberValues,
      FollowerObservationStageMeasurabilityRepair.representativeValues,
      index, values, saved, state] using congrArg
        (fun code => FollowerObservationStageMeasurabilityRepair.ObservationResultCode.occupied
          (FollowerServiceMeasurability.occupiedRoundCodeOfServiceCode rate code)) hcode

private theorem observeOrdinaryCarriedOutputAtComponents_eq_of_local_reads
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (carry : DeclaredFollowerObservationMeasurability.CarriedState p rate)
    (memory : FollowerLifecycleMeasurability.LocalMemoryCode p)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : DeclaredFollowerObservationMeasurability.FollowerActiveCalendarTime p activation)
    (feedback : Fin (D p + 1)) (arm : Fin p.K)
    (hslot : PublicDiscreteDraws.slotDraw (row.2 time.1).1 =
      PublicDiscreteDraws.slotDraw (row'.2 time.1).1)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 time.1).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 time.1).1)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time.1).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time.1).1)
    (hpilots : ∀ player : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 time.1).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 time.1).1)
    (hsource : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      (row.2 time.1).1 = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (row'.2 time.1).1)
    (hthin : (row.2 time.1).1 ContinuousControlSlice.Label.thin =
      (row'.2 time.1).1 ContinuousControlSlice.Label.thin)
    (hprop : (row.2 time.1).1 ContinuousControlSlice.Label.prop =
      (row'.2 time.1).1 ContinuousControlSlice.Label.prop)
    (hsample : (row.2 time.1).2 (0, i) = (row'.2 time.1).2 (0, i))
    (hpast : ∀ j : Fin p.T, j.val < time.1.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (row'.2 j).1 ContinuousControlSlice.Label.prop) :
    DeclaredFollowerObservationMeasurability.observeOrdinaryCarriedOutputAtComponents
      rate i activation (fun _ => carry) (fun _ => memory) (fun _ => row)
        (fun _ => time) (fun _ => feedback) (fun _ => arm) () =
    DeclaredFollowerObservationMeasurability.observeOrdinaryCarriedOutputAtComponents
      rate i activation (fun _ => carry) (fun _ => memory) (fun _ => row')
        (fun _ => time) (fun _ => feedback) (fun _ => arm) () := by
  classical
  let code := FollowerObservationStageMeasurabilityRepair.observationResultCode rate i activation
    (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row time feedback arm)
  let code' := FollowerObservationStageMeasurabilityRepair.observationResultCode rate i activation
    (FollowerObservationStageMeasurabilityRepair.assembleObservationInput
      carry row' time feedback arm)
  have hcode := observationResultCode_eq_of_local_reads
    (rate := rate) i activation carry row row' time feedback arm
    hslot hselected hpilots hsource hthin hsample hpast
  have hsaved : DeclaredFollowerObservationMeasurability.currentSavedScalar row time.1 feedback =
      DeclaredFollowerObservationMeasurability.currentSavedScalar row' time.1 feedback := by
    simp [DeclaredFollowerObservationMeasurability.currentSavedScalar, hthin]
  let key : DeclaredFollowerObservationMeasurability.ObservationKey p :=
    (time.1.val + 1, arm)
  unfold DeclaredFollowerObservationMeasurability.observeOrdinaryCarriedOutputAtComponents
  dsimp only [code, code']
  rw [hcode, hsaved]
  let stage := DeclaredFollowerObservationMeasurability.firstStageCarriedResult code' carry key
    (DeclaredFollowerObservationMeasurability.currentSavedScalar row' time.1 feedback)
  change DeclaredFollowerObservationMeasurability.releaseAfterFirstStage rate i stage
      (carry, (memory, (row, (time.1, feedback)))) =
    DeclaredFollowerObservationMeasurability.releaseAfterFirstStage rate i stage
      (carry, (memory, (row', (time.1, feedback))))
  cases hstageValue : stage with
  | inl reason =>
      unfold DeclaredFollowerObservationMeasurability.releaseAfterFirstStage
      simp
  | inr postService =>
      have hrelease := releaseAndFinishCodeAt_eq_of_local_reads
        (rate := rate) i carry postService memory row row' time.1 feedback
        hslot hselected htuple hpilots hprop
      unfold DeclaredFollowerObservationMeasurability.releaseAfterFirstStage
      simpa [stage, hstageValue] using congrArg
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput postService)
        hrelease

private theorem observeVaryingCarriedOutputAtComponents_eq_of_local_reads
    (i : Fin (p.m - 1))
    (activation activation' : ReferencePrelaunchFollower.Activation p)
    (incoming incoming' : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (hvalid' : activation'.val ≤ calendarIndex.val + 1)
    (arm arm' : Fin p.K) (feedback feedback' : Fin (D p + 1))
    (hactivation : activation = activation') (hincoming : incoming = incoming')
    (harm : arm = arm') (hfeedback : feedback = feedback')
    (hslot : PublicDiscreteDraws.slotDraw (row.2 calendarIndex).1 =
      PublicDiscreteDraws.slotDraw (row'.2 calendarIndex).1)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (row.2 calendarIndex).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 calendarIndex).1)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 calendarIndex).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 calendarIndex).1)
    (hpilots : ∀ player : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) player (row.2 calendarIndex).1 =
        PublicDiscreteDraws.pilotDraw (K_pos p) player (row'.2 calendarIndex).1)
    (hsource : PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
      (row.2 calendarIndex).1 = PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        (row'.2 calendarIndex).1)
    (hthin : (row.2 calendarIndex).1 ContinuousControlSlice.Label.thin =
      (row'.2 calendarIndex).1 ContinuousControlSlice.Label.thin)
    (hprop : (row.2 calendarIndex).1 ContinuousControlSlice.Label.prop =
      (row'.2 calendarIndex).1 ContinuousControlSlice.Label.prop)
    (hsample : (row.2 calendarIndex).2 (0, i) = (row'.2 calendarIndex).2 (0, i))
    (hpast : ∀ j : Fin p.T, j.val < calendarIndex.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (row'.2 j).1 ContinuousControlSlice.Label.prop) :
    DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
      rate i (fun _ : Unit => activation) (fun _ => incoming) (fun _ => row)
      (fun _ => calendarIndex) (fun _ => arm) (fun _ => feedback)
      (by intro _; exact hvalid) () =
    DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
      rate i (fun _ : Unit => activation') (fun _ => incoming') (fun _ => row')
      (fun _ => calendarIndex) (fun _ => arm') (fun _ => feedback')
      (by intro _; exact hvalid') () := by
  cases hactivation
  cases hincoming
  cases harm
  cases hfeedback
  classical
  let time : DeclaredFollowerObservationMeasurability.FollowerActiveCalendarTime p activation :=
    ⟨calendarIndex, hvalid⟩
  unfold DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
  dsimp only [DeclaredFollowerObservationMeasurability.activeCalendarTimeOnFiberLocal]
  apply Sigma.ext
  · rfl
  · cases incoming with
    | none =>
        simp [DeclaredFollowerObservationMeasurability.observeCarriedOutputAtComponents,
          FollowerPrepareJointMeasurability.incomingConfigurationToSum,
          MeasurableEquiv.sumProdDistrib, Equiv.sumProdDistrib]
    | some data =>
        rcases data with ⟨carry, memory⟩
        have hordinary := observeOrdinaryCarriedOutputAtComponents_eq_of_local_reads
          (rate := rate) i activation carry memory row row' time feedback arm
          hslot hselected htuple hpilots hsource hthin hprop hsample hpast
        simpa [DeclaredFollowerObservationMeasurability.observeCarriedOutputAtComponents,
          FollowerPrepareJointMeasurability.incomingConfigurationToSum,
          DeclaredFollowerObservationMeasurability.observeOrdinaryCarriedOutputAtComponents,
          DeclaredFollowerObservationMeasurability.ordinaryOutputToIncoming,
          DeclaredFollowerObservationMeasurability.activeCalendarTimeOnFiberLocal,
          MeasurableEquiv.sumProdDistrib, Equiv.sumProdDistrib, time] using congrArg
            (fun output => (arm,
              DeclaredFollowerObservationMeasurability.ordinaryOutputToIncoming output))
            hordinary

private theorem observeVaryingCarriedOutputAtComponents_none_eq
    (i : Fin (p.m - 1))
    (activation activation' : ReferencePrelaunchFollower.Activation p)
    (incoming incoming' : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1)
    (hvalid' : activation'.val ≤ calendarIndex.val + 1)
    (arm arm' : Fin p.K) (feedback feedback' : Fin (D p + 1))
    (hactivation : activation = activation') (hincoming : incoming = incoming')
    (harm : arm = arm') (hfeedback : feedback = feedback')
    (hnone : incoming = none) :
    DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
      rate i (fun _ : Unit => activation) (fun _ => incoming) (fun _ => row)
      (fun _ => calendarIndex) (fun _ => arm) (fun _ => feedback)
      (by intro _; exact hvalid) () =
    DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
      rate i (fun _ : Unit => activation') (fun _ => incoming') (fun _ => row')
      (fun _ => calendarIndex) (fun _ => arm') (fun _ => feedback')
      (by intro _; exact hvalid') () := by
  cases hactivation
  cases hincoming
  cases harm
  cases hfeedback
  cases hnone
  simp [DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents,
    DeclaredFollowerObservationMeasurability.activeCalendarTimeOnFiberLocal,
    DeclaredFollowerObservationMeasurability.observeCarriedOutputAtComponents,
    FollowerPrepareJointMeasurability.incomingConfigurationToSum,
    MeasurableEquiv.sumProdDistrib, Equiv.sumProdDistrib]

private theorem declaredLocalInput_not_bootstrap
    {block : Fin (n_boot p)} {cursor : Nat}
    (x : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (rowIndex : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hlocal : ActualPostlaunchFollowerMeasurability.localFollower x =
      .declared rowIndex activation configuration) :
    x ∉ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet (rate := rate) := by
  have hlocalValue : x.2.1.1 = .declared rowIndex activation configuration := by
    simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal
  have hcode : ActualPostlaunchFollowerMeasurability.localFollowerStateCode
      (rate := rate) x = Sum.inr (rowIndex, (activation,
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration)) := by
    simp [ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
      ActualPostlaunchFollowerMeasurability.localFollower,
      ActualInitializationRoundMeasurability.followerCodeOfState, hlocalValue]
  simp only [ActualPostlaunchFollowerMeasurability.bootstrapLocalSet, Set.mem_ofPred_eq]
  rw [hcode]
  rintro ⟨startup, heq⟩
  cases heq

private theorem declaredObservationCodeOnCursor_eq_of_own_coordinates
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (rowIndex : Fin (M p)) (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hlocal : ActualPostlaunchFollowerMeasurability.localFollower x =
      .declared rowIndex activation configuration)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hp : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x')
    (ho : observationSourceCoordinates (rate := rate) hcursor i x =
      observationSourceCoordinates (rate := rate) hcursor i x')
    (hy : ActualPostlaunchFollowerMeasurability.localFeedback x =
      ActualPostlaunchFollowerMeasurability.localFeedback x') :
    ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
        (rate := rate) hcursor i ⟨x,
          declaredLocalInput_not_bootstrap (rate := rate) x rowIndex activation
            configuration hlocal⟩ =
    ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
        (rate := rate) hcursor i ⟨x',
          declaredLocalInput_not_bootstrap (rate := rate) x' rowIndex activation
            configuration (hf.symm.trans hlocal)⟩ := by
  classical
  have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
      .declared rowIndex activation configuration := hf.symm.trans hlocal
  have hlocalValue : x.2.1.1 = .declared rowIndex activation configuration := by
    simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal
  have hlocalValue' : x'.2.1.1 = .declared rowIndex activation configuration := by
    simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal'
  have hx := declaredLocalInput_not_bootstrap x rowIndex activation configuration hlocal
  have hx' := declaredLocalInput_not_bootstrap x' rowIndex activation configuration hlocal'
  let branch : ↥((ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
      (rate := rate) (block := block) (cursor := cursor))ᶜ) := ⟨x, hx⟩
  let branch' : ↥((ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
      (rate := rate) (block := block) (cursor := cursor))ᶜ) := ⟨x', hx'⟩
  let fields := ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
    (rate := rate) branch
  let fields' := ActualPostlaunchFollowerMeasurability.declaredCodeOnBootstrapComplement
    (rate := rate) branch'
  have hcode := ActualPostlaunchFollowerMeasurability.followerStateCode_eq_inr_on_bootstrap_complement
    (rate := rate) branch
  have hlocalCode : ActualPostlaunchFollowerMeasurability.localFollowerStateCode
      (rate := rate) x = Sum.inr (rowIndex,
        (activation, FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
          rate configuration)) := by
    simp [ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
      ActualPostlaunchFollowerMeasurability.localFollower,
      ActualInitializationRoundMeasurability.followerCodeOfState, hlocalValue]
  have hfieldsValue : fields = (rowIndex,
      (activation, FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
        rate configuration)) := by
    apply Sum.inr.inj
    exact hcode.symm.trans hlocalCode
  have hcode' := ActualPostlaunchFollowerMeasurability.followerStateCode_eq_inr_on_bootstrap_complement
    (rate := rate) branch'
  have hlocalCode' : ActualPostlaunchFollowerMeasurability.localFollowerStateCode
      (rate := rate) x' = Sum.inr (rowIndex,
        (activation, FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
          rate configuration)) := by
    simp [ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
      ActualPostlaunchFollowerMeasurability.localFollower,
      ActualInitializationRoundMeasurability.followerCodeOfState, hlocalValue']
  have hfieldsValue' : fields' = (rowIndex,
      (activation, FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
        rate configuration)) := by
    apply Sum.inr.inj
    exact hcode'.symm.trans hlocalCode'
  have hrowIndex : fields.1 = rowIndex := congrArg Prod.fst hfieldsValue
  have hrowIndex' : fields'.1 = rowIndex := congrArg Prod.fst hfieldsValue'
  let row := ActualBootstrapObservationCode.sourceRows p
    (ActualPostlaunchFollowerMeasurability.localSource x) fields.1
  let row' := ActualBootstrapObservationCode.sourceRows p
    (ActualPostlaunchFollowerMeasurability.localSource x') fields'.1
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
  have hvalid := ActualPostlaunchFollowerMeasurability.declaredActivation_le_time_of_code
    (rate := rate) hcursor x fields
    (ActualPostlaunchFollowerMeasurability.followerStateCode_eq_inr_on_bootstrap_complement
      (rate := rate) branch)
  have hvalid' := ActualPostlaunchFollowerMeasurability.declaredActivation_le_time_of_code
    (rate := rate) hcursor x' fields'
    (ActualPostlaunchFollowerMeasurability.followerStateCode_eq_inr_on_bootstrap_complement
      (rate := rate) branch')
  let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      fields.2.1 fields.2.2 row time hvalid)
  let output' := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      fields'.2.1 fields'.2.2 row' time hvalid')
  have hprepared := ActualPostlaunchFollowerPreparationLocality.preparedCodeOnCursor_eq_of_own_coordinates
    (rate := rate) hcursor i x x' hf hp
  simp only [ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor,
    dite_eq_right hx, dite_eq_right hx'] at hprepared
  simp only [ActualPostlaunchFollowerMeasurability.preparedCodeOnDeclared] at hprepared
  have hpreparedParts :
      (Sum.inr (α := ActualInitializationPreparationMeasurability.PreparedBootstrapCode p block)
        (fields.1, (fields.2.1, (output.2.2.1, output.2.2.2))) :
          ActualPostlaunchFollowerMeasurability.PreparedFollowerCode p rate block) =
        Sum.inr (α := ActualInitializationPreparationMeasurability.PreparedBootstrapCode p block)
          (fields'.1, (fields'.2.1, (output'.2.2.1, output'.2.2.2))) := by
    simpa [fields, fields', branch, branch', output, output', row, row', time,
      FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
      hvalid, hvalid'] using hprepared
  have hparts := Sum.inr.inj hpreparedParts
  have houtput : (output.2.2.1, output.2.2.2) =
      (output'.2.2.1, output'.2.2.2) := congrArg (fun z => z.2.2) hparts
  have harm : output.2.2.1 = output'.2.2.1 := congrArg Prod.fst houtput
  have hincoming : output.2.2.2 = output'.2.2.2 := congrArg Prod.snd houtput
  have hactivation : fields.2.1 = fields'.2.1 := by
    exact (congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.1)
      hfieldsValue).trans
        (congrArg (fun z : ActualPostlaunchFollowerMeasurability.DeclaredCode p rate => z.2.1)
          hfieldsValue').symm
  have hobserveActual :
      DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
          rate i (fun _ : Unit => fields.2.1) (fun _ => output.2.2.2)
          (fun _ => row) (fun _ => time) (fun _ => output.2.2.1)
          (fun _ => ActualPostlaunchFollowerMeasurability.localFeedback x)
          (by intro _; exact hvalid) () =
      DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
          rate i (fun _ : Unit => fields'.2.1) (fun _ => output'.2.2.2)
          (fun _ => row') (fun _ => time) (fun _ => output'.2.2.1)
          (fun _ => ActualPostlaunchFollowerMeasurability.localFeedback x')
          (by intro _; exact hvalid') () := by
    cases configuration with
    | dagger =>
        have hnone : output.2.2.2 = none := by
          simp [output, FollowerVaryingActivationMeasurability.varyingPreparedOutput,
            FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
            FollowerPrepareJointMeasurability.prepareOutputOnInput,
            FollowerPrepareJointMeasurability.prepareOutputConfiguration,
            FollowerPrepareJointMeasurability.assemblePrepareInput,
            FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
            fields, hfieldsValue]
        exact observeVaryingCarriedOutputAtComponents_none_eq
          (rate := rate) i fields.2.1 fields'.2.1 output.2.2.2 output'.2.2.2
          row row' time hvalid hvalid' output.2.2.1 output'.2.2.1
          (ActualPostlaunchFollowerMeasurability.localFeedback x)
          (ActualPostlaunchFollowerMeasurability.localFeedback x')
          hactivation hincoming harm hy hnone
    | ordinary state memory =>
        have hreads := declaredObservationCoordinates_eq_readFacts
          (rate := rate) hcursor i x x' rowIndex activation state memory
          (by simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal)
          hf hp ho
        have hreads' : PublicDiscreteDraws.slotDraw (row.2 time).1 =
            PublicDiscreteDraws.slotDraw (row'.2 time).1 ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 time).1 =
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (row'.2 time).1 ∧
          OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1 =
            OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row'.2 time).1 ∧
          (∀ player : Fin p.m, PublicDiscreteDraws.pilotDraw (K_pos p) player
            (row.2 time).1 = PublicDiscreteDraws.pilotDraw (K_pos p) player
              (row'.2 time).1) ∧
          PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (row.2 time).1 =
            PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (row'.2 time).1 ∧
          (row.2 time).1 ContinuousControlSlice.Label.rec =
            (row'.2 time).1 ContinuousControlSlice.Label.rec ∧
          (row.2 time).1 ContinuousControlSlice.Label.thin =
            (row'.2 time).1 ContinuousControlSlice.Label.thin ∧
          (row.2 time).1 ContinuousControlSlice.Label.prop =
            (row'.2 time).1 ContinuousControlSlice.Label.prop ∧
          (row.2 time).2 (0, i) = (row'.2 time).2 (0, i) ∧
          (∀ j : Fin p.T, j.val < time.val →
            (row.2 j).1 ContinuousControlSlice.Label.prop =
              (row'.2 j).1 ContinuousControlSlice.Label.prop) := by
          simpa [row, row', time, hrowIndex, hrowIndex'] using hreads
        rcases hreads' with ⟨hslot, hselected, htuple, hpilots, hsource, hrec, hthin,
          hprop, hsample, hpast⟩
        have hobserve := observeVaryingCarriedOutputAtComponents_eq_of_local_reads
          (rate := rate) i fields.2.1 fields'.2.1 output.2.2.2 output'.2.2.2
          row row' time hvalid hvalid' output.2.2.1 output'.2.2.1
          (ActualPostlaunchFollowerMeasurability.localFeedback x)
          (ActualPostlaunchFollowerMeasurability.localFeedback x')
          hactivation hincoming harm hy hslot hselected htuple hpilots hsource
          hthin hprop hsample hpast
        simpa [DeclaredFollowerObservationMeasurability.activeCalendarTimeOnFiberLocal]
          using hobserve
  have hdeclared :
      ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
          (rate := rate) hcursor i branch =
        ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
          (rate := rate) hcursor i branch' := by
    unfold ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
    have hinr := congrArg
      (Sum.inr : DeclaredFollowerObservationMeasurability.VaryingObserveCarriedOutput p rate →
        ActualPostlaunchFollowerMeasurability.FollowerObservationCode p rate block)
      hobserveActual
    simpa [fields, fields', branch, branch', row, row', time, output, output',
      FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
      hvalid, hvalid'] using hinr
  have hdeclared' :
      ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
          (rate := rate) hcursor i ⟨x, hx⟩ =
        ActualPostlaunchFollowerMeasurability.declaredObservationCodeOnCursor
          (rate := rate) hcursor i ⟨x', hx'⟩ := by
    simpa [branch, branch'] using hdeclared
  exact hdeclared'

private theorem bootstrapObserve_eq_of_active_update
    (s : Fin (n_boot p)) (state : ActualBootstrapObservationCode.StartupCode p s)
    (ids ids' : CompletePublicTable.IDArray p)
    (rows rows' : CompletePublicTable.CompleteRows p)
    (time : Fin p.T) (observation observation' : ReferencePrelaunchFollower.Observation p)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers)
    (hstay : BootstrapObservedFollower.positiveStay ids privateID time observation =
      BootstrapObservedFollower.positiveStay ids' privateID time observation')
    (hadvance : BootstrapObservedFollower.observationAdvance p s ids rows true privateID
        registers time observation =
      BootstrapObservedFollower.observationAdvance p s ids' rows' true privateID
        registers time observation') :
    BootstrapObservedFollower.observe p s state ids rows time observation =
      BootstrapObservedFollower.observe p s state ids' rows' time observation' := by
  classical
  cases hvalidation : BootstrapObservedFollower.validateRound p s state time with
  | failure error => simp [BootstrapObservedFollower.observe, hvalidation]
  | next hin hopen hnext =>
      simp [BootstrapObservedFollower.observe, BootstrapObservedFollower.observeOne,
        BootstrapObservedFollower.observeBlockCase, hvalidation, hactive, hstay, hadvance]

/-- On the bootstrap branch, the actual observation code depends only on
this follower's current private ID, its own finite-grid feedback, and the
candidate evidence retained below. In particular, when the incoming
candidate registers are pending, the existing update does not read candidate
rows, while its positive-feedback gain is still preserved. -/
private theorem bootstrapObservationCodeOnCursor_eq_of_own_coordinates
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (startup : ActualBootstrapObservationCode.StartupCode p block)
    (hlocal : ActualPostlaunchFollowerMeasurability.localFollower x = .bootstrap startup)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (ho : observationSourceCoordinates (rate := rate) hcursor i x =
      observationSourceCoordinates (rate := rate) hcursor i x')
    (hy : ActualPostlaunchFollowerMeasurability.localFeedback x =
      ActualPostlaunchFollowerMeasurability.localFeedback x') :
    ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
        (rate := rate) hcursor i x' := by
  classical
  have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
      .bootstrap startup := hf.symm.trans hlocal
  have hlocalValue : x.2.1.1 = .bootstrap startup := by
    simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal
  have hlocalValue' : x'.2.1.1 = .bootstrap startup := by
    simpa [ActualPostlaunchFollowerMeasurability.localFollower] using hlocal'
  have hx : x ∈ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
      (rate := rate) := by
    change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
      (rate := rate) x ∈ Set.range Sum.inl
    unfold ActualPostlaunchFollowerMeasurability.localFollowerStateCode
    rw [hlocal]
    simp [ActualInitializationRoundMeasurability.followerCodeOfState]
  have hx' : x' ∈ ActualPostlaunchFollowerMeasurability.bootstrapLocalSet
      (rate := rate) := by
    change ActualPostlaunchFollowerMeasurability.localFollowerStateCode
      (rate := rate) x' ∈ Set.range Sum.inl
    unfold ActualPostlaunchFollowerMeasurability.localFollowerStateCode
    rw [hlocal']
    simp [ActualInitializationRoundMeasurability.followerCodeOfState]
  have hstartup : ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap
      (rate := rate) ⟨x, hx⟩ = startup := by
    simp [ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap,
      ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
      ActualPostlaunchFollowerMeasurability.localFollower, hlocalValue,
      ActualInitializationRoundMeasurability.followerCodeOfState]
  have hstartup' : ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap
      (rate := rate) ⟨x', hx'⟩ = startup := by
    simp [ActualPostlaunchFollowerMeasurability.startupCodeOnBootstrap,
      ActualPostlaunchFollowerMeasurability.localFollowerStateCode,
      ActualPostlaunchFollowerMeasurability.localFollower, hlocalValue',
      ActualInitializationRoundMeasurability.followerCodeOfState]
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor
  let ids := ActualBootstrapObservationCode.sourceIDs p
    (ActualPostlaunchFollowerMeasurability.localSource x)
  let ids' := ActualBootstrapObservationCode.sourceIDs p
    (ActualPostlaunchFollowerMeasurability.localSource x')
  let rows := ActualBootstrapObservationCode.sourceRows p
    (ActualPostlaunchFollowerMeasurability.localSource x)
  let rows' := ActualBootstrapObservationCode.sourceRows p
    (ActualPostlaunchFollowerMeasurability.localSource x')
  cases hcase : startup.blockCase with
  | inactive =>
      have hobserve : BootstrapObservedFollower.observe p block startup ids rows time
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ActualPostlaunchFollowerMeasurability.localFeedback x)) =
        BootstrapObservedFollower.observe p block startup ids' rows' time
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ActualPostlaunchFollowerMeasurability.localFeedback x')) := by
        cases hvalidation : BootstrapObservedFollower.validateRound p block startup time with
        | failure error => simp [BootstrapObservedFollower.observe, hvalidation]
        | next hin hopen hnext =>
            simp [BootstrapObservedFollower.observe, BootstrapObservedFollower.observeOne,
              BootstrapObservedFollower.observeBlockCase, hvalidation, hcase]
      have hcode : ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
          (rate := rate) hcursor i ⟨x, hx⟩ =
        ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
          (rate := rate) hcursor i ⟨x', hx'⟩ := by
        unfold ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
        rw [hstartup, hstartup']
        exact congrArg Sum.inl hobserve
      simpa [ActualPostlaunchFollowerMeasurability.observationCodeOnCursor, hx, hx'] using hcode
  | active held privateID gain registers =>
      have hcoordinates :
          (ids privateID time,
            if registers.pending.isSome then none else
              some (fun candidate =>
                (((rows candidate).2 time).1 ContinuousControlSlice.Label.slot,
                  (rows candidate).1 privateID time))) =
          (ids' privateID time,
            if registers.pending.isSome then none else
              some (fun candidate =>
                (((rows' candidate).2 time).1 ContinuousControlSlice.Label.slot,
                  (rows' candidate).1 privateID time))) := by
        simpa [observationSourceCoordinates,
          ActualPostlaunchFollowerMeasurability.localFollower,
          ActualPostlaunchFollowerMeasurability.localSource,
          hlocalValue, hlocalValue', hcase, time, ids, ids', rows, rows'] using ho
      have hid : ids privateID time = ids' privateID time :=
        congrArg Prod.fst hcoordinates
      have hpositive : ActualBootstrapObservationCode.observationPositiveFlag p
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ActualPostlaunchFollowerMeasurability.localFeedback x)) =
        ActualBootstrapObservationCode.observationPositiveFlag p
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ActualPostlaunchFollowerMeasurability.localFeedback x')) := by
        rw [hy]
      have hstayPositive :
          (0 < (ActualInitializationPhysicalStep.observationOfGrid p
              (ActualPostlaunchFollowerMeasurability.localFeedback x)).val.val) ↔
            (0 < (ActualInitializationPhysicalStep.observationOfGrid p
              (ActualPostlaunchFollowerMeasurability.localFeedback x')).val.val) := by
        have h := congrArg (fun b : Bool => b = true) hpositive
        simpa [ActualBootstrapObservationCode.observationPositiveFlag] using h
      have hstay : BootstrapObservedFollower.positiveStay ids privateID time
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ActualPostlaunchFollowerMeasurability.localFeedback x)) =
        BootstrapObservedFollower.positiveStay ids' privateID time
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ActualPostlaunchFollowerMeasurability.localFeedback x')) := by
        apply propext
        simp [BootstrapObservedFollower.positiveStay, hid, hstayPositive]
      cases hpending : registers.pending with
      | some _ =>
          have hadvance : BootstrapObservedFollower.observationAdvance p block ids rows true
              privateID registers time
              (ActualInitializationPhysicalStep.observationOfGrid p
                (ActualPostlaunchFollowerMeasurability.localFeedback x)) =
            BootstrapObservedFollower.observationAdvance p block ids' rows' true
              privateID registers time
              (ActualInitializationPhysicalStep.observationOfGrid p
                (ActualPostlaunchFollowerMeasurability.localFeedback x')) := by
            simp [BootstrapObservedFollower.observationAdvance, hpending]
          have hobserve := bootstrapObserve_eq_of_active_update block startup ids ids' rows rows'
            time (ActualInitializationPhysicalStep.observationOfGrid p
              (ActualPostlaunchFollowerMeasurability.localFeedback x))
            (ActualInitializationPhysicalStep.observationOfGrid p
              (ActualPostlaunchFollowerMeasurability.localFeedback x')) held privateID gain
            registers hcase hstay hadvance
          have hcode : ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
              (rate := rate) hcursor i ⟨x, hx⟩ =
            ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
              (rate := rate) hcursor i ⟨x', hx'⟩ := by
            unfold ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
            rw [hstartup, hstartup']
            exact congrArg Sum.inl hobserve
          simpa [ActualPostlaunchFollowerMeasurability.observationCodeOnCursor, hx, hx'] using hcode
      | none =>
          have hcodeLeft := congrArg Prod.snd hcoordinates
          have hcandidate : (fun candidate : Fin (M p) =>
              (((rows candidate).2 time).1 ContinuousControlSlice.Label.slot,
                (rows candidate).1 privateID time)) =
            (fun candidate : Fin (M p) =>
              (((rows' candidate).2 time).1 ContinuousControlSlice.Label.slot,
                (rows' candidate).1 privateID time)) := by
            have hsome : some (fun candidate : Fin (M p) =>
                (((rows candidate).2 time).1 ContinuousControlSlice.Label.slot,
                  (rows candidate).1 privateID time)) =
              some (fun candidate : Fin (M p) =>
                (((rows' candidate).2 time).1 ContinuousControlSlice.Label.slot,
                  (rows' candidate).1 privateID time)) := by
              simpa [hpending] using hcodeLeft
            exact Option.some.inj hsome
          have hslot (candidate : Fin (M p)) :
              ((rows candidate).2 time).1 ContinuousControlSlice.Label.slot =
                ((rows' candidate).2 time).1 ContinuousControlSlice.Label.slot :=
            congrArg Prod.fst (congrFun hcandidate candidate)
          have hforward (candidate : Fin (M p)) :
              (rows candidate).1 privateID time = (rows' candidate).1 privateID time :=
            congrArg Prod.snd (congrFun hcandidate candidate)
          have hslotDraw (candidate : Fin (M p)) :
              PublicDiscreteDraws.slotDraw ((rows candidate).2 time).1 =
                PublicDiscreteDraws.slotDraw ((rows' candidate).2 time).1 := by
            unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
            rw [hslot candidate]
          have hdata (candidate : Fin (M p)) :
              BootstrapAllCandidateController.rowIsData rows candidate time =
                BootstrapAllCandidateController.rowIsData rows' candidate time := by
            unfold BootstrapAllCandidateController.rowIsData
            rw [hslotDraw candidate]
          have hadvance : BootstrapObservedFollower.observationAdvance p block ids rows true
              privateID registers time
              (ActualInitializationPhysicalStep.observationOfGrid p
                (ActualPostlaunchFollowerMeasurability.localFeedback x)) =
            BootstrapObservedFollower.observationAdvance p block ids' rows' true
              privateID registers time
              (ActualInitializationPhysicalStep.observationOfGrid p
                (ActualPostlaunchFollowerMeasurability.localFeedback x')) := by
            have hupdate : BootstrapObservedFollower.updateObservedEvidence p block ids rows true
                privateID registers time
                (ActualInitializationPhysicalStep.observationOfGrid p
                  (ActualPostlaunchFollowerMeasurability.localFeedback x)) =
              BootstrapObservedFollower.updateObservedEvidence p block ids' rows' true privateID
                registers time
                (ActualInitializationPhysicalStep.observationOfGrid p
                  (ActualPostlaunchFollowerMeasurability.localFeedback x')) := by
              apply BootstrapAllCandidateController.registers_ext
              · intro candidate
                simp [BootstrapObservedFollower.updateObservedEvidence,
                  BootstrapObservedFollower.observedCandidateEligible, hstay,
                  hdata candidate]
              · intro candidate
                simp [BootstrapObservedFollower.updateObservedEvidence,
                  BootstrapObservedFollower.observedCandidateEligible, hstay,
                  hdata candidate, hforward candidate]
              · rfl
            have hcondition :
                (time ∈ BootstrapDimensions.calendarBlock p block ∧
                  BootstrapObservedFollower.positiveStay ids privateID time
                    (ActualInitializationPhysicalStep.observationOfGrid p
                      (ActualPostlaunchFollowerMeasurability.localFeedback x))) =
                (time ∈ BootstrapDimensions.calendarBlock p block ∧
                  BootstrapObservedFollower.positiveStay ids' privateID time
                    (ActualInitializationPhysicalStep.observationOfGrid p
                      (ActualPostlaunchFollowerMeasurability.localFeedback x'))) :=
              congrArg (fun positive =>
                time ∈ BootstrapDimensions.calendarBlock p block ∧ positive) hstay
            simp [BootstrapObservedFollower.observationAdvance, hpending,
              hcondition, hupdate]
          have hobserve := bootstrapObserve_eq_of_active_update block startup ids ids' rows rows'
            time (ActualInitializationPhysicalStep.observationOfGrid p
              (ActualPostlaunchFollowerMeasurability.localFeedback x))
            (ActualInitializationPhysicalStep.observationOfGrid p
              (ActualPostlaunchFollowerMeasurability.localFeedback x')) held privateID gain
            registers hcase hstay hadvance
          have hcode : ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
              (rate := rate) hcursor i ⟨x, hx⟩ =
            ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
              (rate := rate) hcursor i ⟨x', hx'⟩ := by
            unfold ActualPostlaunchFollowerMeasurability.bootstrapObservationCodeOnCursor
            rw [hstartup, hstartup']
            exact congrArg Sum.inl hobserve
          simpa [ActualPostlaunchFollowerMeasurability.observationCodeOnCursor, hx, hx'] using hcode

/-- Equal incoming own storage, literal preparation/observation coordinates,
and own feedback give the exact PREPARE, observation and whole successor code.
These four equalities are explicit conditional internal inputs. -/
theorem localCodeOnCursor_eq_of_own_coordinates
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hp : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x')
    (ho : observationSourceCoordinates (rate := rate) hcursor i x =
      observationSourceCoordinates (rate := rate) hcursor i x')
    (hy : ActualPostlaunchFollowerMeasurability.localFeedback x =
      ActualPostlaunchFollowerMeasurability.localFeedback x') :
    ActualPostlaunchFollowerMeasurability.localCodeOnCursor
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerMeasurability.localCodeOnCursor
        (rate := rate) hcursor i x' := by
  have hprepared :=
    ActualPostlaunchFollowerPreparationLocality.preparedCodeOnCursor_eq_of_own_coordinates
      hcursor i x x' hf hp
  have hobserved : ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
      (rate := rate) hcursor i x =
    ActualPostlaunchFollowerMeasurability.observationCodeOnCursor
      (rate := rate) hcursor i x' := by
    cases hlocal : ActualPostlaunchFollowerMeasurability.localFollower x with
    | bootstrap startup =>
        exact bootstrapObservationCodeOnCursor_eq_of_own_coordinates
          hcursor i x x' startup hlocal hf ho hy
    | declared rowIndex activation configuration =>
        have hx := declaredLocalInput_not_bootstrap x rowIndex activation
          configuration hlocal
        have hx' := declaredLocalInput_not_bootstrap x' rowIndex activation
          configuration (hf.symm.trans hlocal)
        have hdeclared := declaredObservationCodeOnCursor_eq_of_own_coordinates
          hcursor i x x' rowIndex activation configuration hlocal hf hp ho hy
        simpa only [ActualPostlaunchFollowerMeasurability.observationCodeOnCursor,
          dite_eq_right hx, dite_eq_right hx'] using hdeclared
  have hpartial :
      ActualPostlaunchFollowerMeasurability.partialSuccessorCodeOnCursor
          (rate := rate) hcursor i x =
        ActualPostlaunchFollowerMeasurability.partialSuccessorCodeOnCursor
          (rate := rate) hcursor i x' := by
    simp only [ActualPostlaunchFollowerMeasurability.partialSuccessorCodeOnCursor]
    rw [hprepared, hobserved]
  have hsuccessor :
      ActualPostlaunchFollowerMeasurability.successorCodeOnCursor
          (rate := rate) hcursor i x =
        ActualPostlaunchFollowerMeasurability.successorCodeOnCursor
          (rate := rate) hcursor i x' := by
    have hleft := ActualPostlaunchFollowerMeasurability.partialSuccessorCode_eq_inr_successorCode
      (rate := rate) hcursor i x
    have hright := ActualPostlaunchFollowerMeasurability.partialSuccessorCode_eq_inr_successorCode
      (rate := rate) hcursor i x'
    exact Sum.inr.inj (hleft.symm.trans (hpartial.trans hright))
  exact Prod.ext hprepared (Prod.ext hobserved hsuccessor)

/-- The actual physical step has equal whole next follower storage under the
same four conditional internal equalities. Only this follower's actual
collision-filtered feedback is equated; no history provenance is assumed. -/
theorem physical_follower_next_eq_of_own_coordinates
    {block : Fin (n_boot p)} {cursor : Nat}
    (i : Fin (p.m - 1))
    (a b : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerMeasurability.localFollower
        (ActualPostlaunchStepMeasurability.followerInput i b))
    (hp : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i b))
    (ho : observationSourceCoordinates (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      observationSourceCoordinates (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i b))
    (hy : ActualPostlaunchFollowerMeasurability.localFeedback
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerMeasurability.localFeedback
        (ActualPostlaunchStepMeasurability.followerInput i b)) :
    (ActualPostlaunchPhysicalStep.step a).nextState.followers i =
      (ActualPostlaunchPhysicalStep.step b).nextState.followers i := by
  have hcursor : a.cursor_lt = b.cursor_lt := Subsingleton.elim _ _
  have hlocalCode := localCodeOnCursor_eq_of_own_coordinates
    (rate := rate) a.cursor_lt i
    (ActualPostlaunchStepMeasurability.followerInput i a)
    (ActualPostlaunchStepMeasurability.followerInput i b)
    hf hp ho hy
  have hsuccessor :
      (ActualPostlaunchStepMeasurability.followerLocalCode i a).2.2 =
        (ActualPostlaunchStepMeasurability.followerLocalCode i b).2.2 := by
    simpa [ActualPostlaunchStepMeasurability.followerLocalCode,
      ActualPostlaunchStepMeasurability.followerInput, hcursor] using
      congrArg (fun code : ActualPostlaunchFollowerMeasurability.LocalCode
        (rate := rate) block => code.2.2) hlocalCode
  have hcodec : Function.Injective
      (ActualInitializationRoundMeasurability.followerCodeOfState p rate block) :=
    Function.LeftInverse.injective
      (ActualInitializationRoundMeasurability.followerStateOfCode_encode p rate block)
  apply hcodec
  change ActualInitializationRoundMeasurability.followerCodeOfState p rate block
      ((ActualPostlaunchPhysicalStep.step a).followers i).next =
    ActualInitializationRoundMeasurability.followerCodeOfState p rate block
      ((ActualPostlaunchPhysicalStep.step b).followers i).next
  rw [← ActualPostlaunchStepMeasurability.followerLocalCode_next a i,
    ← ActualPostlaunchStepMeasurability.followerLocalCode_next b i,
    ActualInitializationCursorMeasurability.followerCodeOfState_decode,
    ActualInitializationCursorMeasurability.followerCodeOfState_decode]
  exact hsuccessor

end Bandits.Support.ActualPostlaunchFollowerObservationLocality

end
