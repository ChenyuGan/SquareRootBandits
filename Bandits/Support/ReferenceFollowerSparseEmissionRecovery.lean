/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerBufferProvenance
public import Bandits.Support.ReferenceFollowerReplyChronology
public import Bandits.Support.ReferenceActiveDataOwnership

/-!
# Conditional sparse-emission recovery on an actual physical interval

Sources: `sources/zip4/manuscript/06_interruptions.tex:195-233,270-275,303-324`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`, and
`sources/zip4/manuscript/05_binary_transport.tex:426-431`.

The interval below is the literal successor slice of the canonical physical
horizon. The carried buffer remains its actual seed plus actual emissions.
Recovery conclusions retain the selected-view interval condition as an
explicit local input. This module does not prove that global selector, physical
assignment ownership, recording/Gamma equality, or initial queue truth.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFollowerBufferProvenance
open Bandits.Support.ReferenceFollowerReplyChronology
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.QueueReplay

namespace Bandits.Support.ReferenceFollowerSparseEmissionRecovery

abbrev Parameters := ReferenceActivePhysicalHorizon.Parameters
abbrev RateInput := ReferenceActivePhysicalHorizon.RateInput
abbrev State (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.State p rate
abbrev RoundRecord {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev BufferRecord (p : Parameters) := SparseCalendarReplay.SparseCalendarRecord p.K

variable {p : Parameters} {rate : RateInput p}

/-- The retained prefix before the selected actual successor round. -/
def priorRun (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) :=
  ReferenceActivePhysicalHorizon.run initial rows selected rewards s k (by omega) hmode

/-- The actual next round record made by the canonical horizon input and
exactly one call to the existing physical step. -/
def successorRecord (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) : RoundRecord (p := p) (rate := rate) := by
  let prior := priorRun initial rows selected rewards s k hspan hmode
  let entry : CalendarEntry p s := ⟨s + k, by omega, by omega⟩
  let input := roundInputAt initial rows selected rewards s hmode prior entry
  exact ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- The physical records from the fixed boundary through its literal next
record. This retains every round in the computed prefix. -/
def physicalRecords (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) :
    List (RoundRecord (p := p) (rate := rate)) :=
  (priorRun initial rows selected rewards s k hspan hmode).records ++
    [successorRecord initial rows selected rewards s k hspan hmode]

/-- The actual selected-view restriction needed to exclude a carried-buffer
reset inside the scan. It concerns only payload fields of actual coordinator
views retained in the prefix. -/
def selectedViewInterval (s : ℕ)
    (records : List (RoundRecord (p := p) (rate := rate))) : Prop :=
  ∀ record ∈ records, ∀ view,
    record.output.preparation.coordinator.downView = some view →
      s ≤ view.payload.sigma.val

/-- A literal fixed-start view at every selected prefix round discharges the
interval restriction, including rounds with no selected view. -/
theorem selectedViewInterval_of_fixed_start (s : ℕ)
    (records : List (RoundRecord (p := p) (rate := rate)))
    (hfixed : ∀ record ∈ records, ∀ view,
      record.output.preparation.coordinator.downView = some view →
        view.payload.sigma.val = s) :
    selectedViewInterval s records := by
  intro record hrecord view hview
  rw [hfixed record hrecord view hview]

/-- The final follower stage carries the exact first-stage DOWN diagnostics
through either final configuration. -/
theorem finishFollower_diagnostics
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).downInput ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  rw [ReferenceActivePhysicalStep.finishFollower, hconfiguration]
  cases hresult : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm
      observation state).result with
  | error failure => simp [hresult]
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation state memory post with
      | error failure => simp [hresult, hfinish]
      | ok result => simp [hresult, hfinish]

/-- An accepted result of the filtered reference cut is installed from its
actual input state. -/
theorem acceptedReferenceCut_before_eq
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (input before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (haccepted :
      (ReferenceDownReception.referenceDownCut p view i row t observation rate input).outcome =
        .accepted before after raw M scan registers lastService) :
    before = input := by
  classical
  unfold ReferenceDownReception.referenceDownCut at haccepted
  split at haccepted
  · split at haccepted
    · split at haccepted
      · split at haccepted
        · split at haccepted
          · dsimp only at haccepted
            split at haccepted
            · dsimp only at haccepted
              split at haccepted
              · cases haccepted
              · split at haccepted
                next ha =>
                  split at haccepted
                  · cases haccepted
                  · cases haccepted
                    rfl
                · cases haccepted
            · cases haccepted
          · cases haccepted
        · cases haccepted
      · cases haccepted
    · cases haccepted
  · cases haccepted

/-- A literal accepted reference DOWN cannot be parsed from the missing
expected word of a `none` selected view. -/
theorem acceptedReferenceCut_someView
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (input before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (haccepted :
      (ReferenceDownReception.referenceDownCut p view i row t observation rate input).outcome =
        .accepted before after raw M scan registers lastService) :
    ∃ selected, view = some selected := by
  cases view with
  | some selected => exact ⟨selected, rfl⟩
  | none =>
      by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
      · by_cases hstatus : input.status = .unoccupied
        · by_cases hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate input
          · by_cases hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p input.downBatch
            · by_cases hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p input.buffer
              · let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                  p i row t observation rate input
                have hcut : (ReferenceDownReception.referenceDownCut p
                    (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                    observation rate input).outcome =
                    .decodeOrParseRejected input { input with downBatch := decoded.1 } decoded.2 := by
                  cases hraw : decoded.2 <;>
                    simp [ReferenceDownReception.referenceDownCut,
                      ReferenceDownReception.expectedDownFlatWord,
                      ReferenceDownReception.ordinaryParse,
                      OrdinaryMessageCodec.parseDown, Option.map,
                      hselected, hstatus,
                      hregisters, hbatch, hbuffer, decoded, hraw]
                rw [hcut] at haccepted
                cases haccepted
              · have hcut : (ReferenceDownReception.referenceDownCut p
                    (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                    observation rate input).outcome =
                    .inputFailure input .sparseBuffer := by
                  simp [ReferenceDownReception.referenceDownCut,
                    ReferenceDownReception.expectedDownFlatWord, hselected, hstatus,
                    hregisters, hbatch, hbuffer]
                rw [hcut] at haccepted
                cases haccepted
            · have hcut : (ReferenceDownReception.referenceDownCut p
                  (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                  observation rate input).outcome =
                  .inputFailure input .decoderBatch := by
                simp [ReferenceDownReception.referenceDownCut,
                  ReferenceDownReception.expectedDownFlatWord, hselected, hstatus,
                  hregisters, hbatch]
              rw [hcut] at haccepted
              cases haccepted
          · have hcut : (ReferenceDownReception.referenceDownCut p
                (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                observation rate input).outcome = .inputFailure input .registers := by
              simp [ReferenceDownReception.referenceDownCut,
                ReferenceDownReception.expectedDownFlatWord, hselected, hstatus,
                hregisters]
            rw [hcut] at haccepted
            cases haccepted
        · have hcut : (ReferenceDownReception.referenceDownCut p
              (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
              observation rate input).outcome = .skipped input .occupiedAtChoice := by
            simp [ReferenceDownReception.referenceDownCut,
              ReferenceDownReception.expectedDownFlatWord, hselected, hstatus]
          rw [hcut] at haccepted
          cases haccepted
      · have hcut : (ReferenceDownReception.referenceDownCut p
            (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
            observation rate input).outcome = .skipped input .notSelectedDown := by
          simp [ReferenceDownReception.referenceDownCut,
            ReferenceDownReception.expectedDownFlatWord, hselected]
        rw [hcut] at haccepted
        cases haccepted

/-- A successful outcome of the actual reference cut forces its raw comparison
to be the matching branch. Thus an accepted result itself rules out the
per-decision raw-mismatch flag. -/
theorem acceptedReferenceCut_not_rawMismatch
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (haccepted :
      (ReferenceDownReception.referenceDownCut p view i row t observation rate state).outcome =
        .accepted state after raw M scan registers lastService) :
    ¬ ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p view i row t observation rate state) := by
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
    p i row t observation rate state
  have hselected : ActiveFollowerDownAcceptance.downSelected p i row t := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row t
        observation rate state).outcome = .skipped state .notSelectedDown := by
      simp [ReferenceDownReception.referenceDownCut, hbad]
    rw [hcut] at haccepted
    cases haccepted
  have hstatus : state.status = .unoccupied := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row t
        observation rate state).outcome = .skipped state .occupiedAtChoice := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hbad]
    rw [hcut] at haccepted
    cases haccepted
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row t
        observation rate state).outcome = .inputFailure state .registers := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hbad]
    rw [hcut] at haccepted
    cases haccepted
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row t
        observation rate state).outcome = .inputFailure state .decoderBatch := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbad]
    rw [hcut] at haccepted
    cases haccepted
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row t
        observation rate state).outcome = .inputFailure state .sparseBuffer := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbad]
    rw [hcut] at haccepted
    cases haccepted
  have hmatches : decoded.2 =
      ReferenceDownReception.expectedDownFlatWord view i row t := by
    by_contra hbad
    have hcut : (ReferenceDownReception.referenceDownCut p view i row t
        observation rate state).outcome = .decodeOrParseRejected state
          { state with downBatch := decoded.1 } decoded.2 := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbuffer, decoded, hbad]
    rw [hcut] at haccepted
    cases haccepted
  have hcomparison :
      (ReferenceDownReception.referenceDownCut p view i row t observation rate state).rawComparison =
        some true := by
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
      hregisters, hbatch, hbuffer, decoded, hmatches]
  intro hmismatch
  change (ReferenceDownReception.referenceDownCut p view i row t observation rate state).rawComparison =
    some false at hmismatch
  rw [hcomparison] at hmismatch
  cases hmismatch

/-- On an actual accepted follower diagnostic, the filtered operation has no
raw mismatch and agrees with the ordinary local DOWN transition. -/
theorem actualAcceptedCut_downTransition
    (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hinput : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted logged after raw M scan registers lastService) :
    ActiveFollowerDownAcceptance.downTransition p
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged =
      .accepted logged after raw M scan registers lastService := by
  let prepared := record.output.preparation.followers.followers i
  let view := record.output.preparation.coordinator.downView
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower
    i record
  rw [hfinish] at hdown
  cases hprepared : prepared.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, prepared, hprepared] at hdown
  | ordinary choice memory =>
      have hdiagnostics := finishFollower_diagnostics view prepared observation
        choice memory hprepared
      rw [hdiagnostics.2] at hdown
      by_cases hunoccupied : choice.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging prepared.follower
            prepared.row prepared.activation prepared.time
            (prepared.arm, observation) choice with
        | error reason =>
            simp [ReferenceActivePhysicalStep.recordFollower, prepared,
              hunoccupied, hlogging] at hdown
        | ok logged' =>
            have hactual := ReferenceActivePhysicalStep.recordFollower_logged
              view prepared.follower prepared.row prepared.activation prepared.time
              prepared.active prepared.arm observation choice logged' hunoccupied hlogging
            have hcut : some cut = some (ReferenceDownReception.referenceDownCut p view
                prepared.follower prepared.row prepared.time observation rate logged') := by
              exact hdown.symm.trans hactual.2
            have hcut' := Option.some.inj hcut
            have hdiagInput : (record.output.followers i).downInput = some logged' := by
              rw [hfinish]
              exact hdiagnostics.1.trans hactual.1
            have hlogged : logged' = logged :=
              Option.some.inj (hdiagInput.symm.trans hinput)
            subst logged'
            have haccepted' := haccepted
            rw [hcut'] at haccepted'
            have hnomismatch := acceptedReferenceCut_not_rawMismatch
              view prepared.follower prepared.row prepared.time observation
              logged after raw M scan registers lastService haccepted'
            have hagree :=
              ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
                view prepared.follower prepared.row prepared.time observation rate logged hnomismatch
            calc
              ActiveFollowerDownAcceptance.downTransition p prepared.follower prepared.row
                  prepared.time observation rate logged =
                  (ReferenceDownReception.referenceDownCut p view prepared.follower
                    prepared.row prepared.time observation rate logged).outcome := hagree.symm
              _ = cut.outcome := by rw [← hcut']
              _ = .accepted logged after raw M scan registers lastService := haccepted
      · simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied] at hdown

/-- An actual DOWN diagnostic forces its literal prepared choice to be
ordinary and unoccupied, and identifies the cut with the call made from that
round's selected view and actual logged state. -/
theorem actualDownDiagnostic_choice
    (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hdown : (record.output.followers i).down = some cut) :
    ∃ choice memory logged,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary choice memory ∧ choice.status = .unoccupied ∧
      ActiveFollowerLogging.checkedLogging
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time
        ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice = .ok logged ∧
      (record.output.followers i).downInput = some logged ∧
      cut = ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged := by
  let prepared := record.output.preparation.followers.followers i
  let view := record.output.preparation.coordinator.downView
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower
    i record
  rw [hfinish] at hdown
  cases hprepared : prepared.configuration with
  | dagger =>
      simp [ReferenceActivePhysicalStep.finishFollower, prepared, hprepared] at hdown
  | ordinary choice memory =>
      have hdiagnostics := finishFollower_diagnostics view prepared observation
        choice memory hprepared
      rw [hdiagnostics.2] at hdown
      by_cases hunoccupied : choice.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging prepared.follower
            prepared.row prepared.activation prepared.time
            (prepared.arm, observation) choice with
        | error reason =>
            simp [ReferenceActivePhysicalStep.recordFollower, prepared,
              hunoccupied, hlogging] at hdown
        | ok logged' =>
            have hactual := ReferenceActivePhysicalStep.recordFollower_logged
              view prepared.follower prepared.row prepared.activation prepared.time
              prepared.active prepared.arm observation choice logged' hunoccupied hlogging
            have hcut : some cut =
                some (ReferenceDownReception.referenceDownCut p view prepared.follower
                  prepared.row prepared.time observation rate logged') := by
              exact hdown.symm.trans hactual.2
            have hcut' := Option.some.inj hcut
            have hdiagInput : (record.output.followers i).downInput = some logged' := by
              rw [hfinish]
              exact hdiagnostics.1.trans hactual.1
            exact ⟨choice, memory, logged', rfl, hunoccupied, hlogging,
              hdiagInput, hcut'⟩
      · simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied] at hdown

/-- The raw comparison flag on an actual accepted follower diagnostic is
forced to its matching branch by inversion of the actual reference parser.
No comparison or match predicate is supplied by the caller. -/
theorem actualAcceptedCut_no_rawMismatch
    (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hinput : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted logged after raw M scan registers lastService) :
    ¬ ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged) := by
  obtain ⟨_, _, actualLogged, _, _, _, hdiagInput, hcut⟩ :=
    actualDownDiagnostic_choice record i cut hdown
  have hactualLogged : actualLogged = logged :=
    Option.some.inj (hdiagInput.symm.trans hinput)
  subst actualLogged
  have haccepted' := haccepted
  rw [hcut] at haccepted'
  exact acceptedReferenceCut_not_rawMismatch
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    logged after raw M scan registers lastService haccepted'

/-- A valid actual accepted DOWN at the successor excludes every accepted
DOWN reset in the preceding actual prefix, provided each actual selected view
there starts no earlier than the fixed boundary. The selected-view restriction
is explicit; it is not bundled with seed validity or a run-wide truth premise.
-/
theorem accepted_window_no_prior_reset
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hcurrentInput :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).downInput =
        some logged)
    (hcurrentDown :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).down =
        some cut)
    (hcurrentAccepted :
      cut.outcome = .accepted logged after raw M scan registers lastService)
    (hcurrentSigma : M.val.sigma = s + 1)
    (hwindow : selectedViewInterval s
      (priorRun initial rows selected rewards s k hspan hmode).records) :
    ∀ record ∈ (priorRun initial rows selected rewards s k hspan hmode).records,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
  let prior := priorRun initial rows selected rewards s k hspan hmode
  let current := successorRecord initial rows selected rewards s k hspan hmode
  obtain ⟨choice, choiceMemory, currentLogged, hprepared, hunoccupied,
      hlogging, hdiagInput, hcut⟩ :=
    actualDownDiagnostic_choice current i cut hcurrentDown
  have hcurrentLogged : currentLogged = logged :=
    Option.some.inj (hdiagInput.symm.trans hcurrentInput)
  subst currentLogged
  have hcurrentAccepted' := hcurrentAccepted
  rw [hcut] at hcurrentAccepted'
  have haccepted := ReferenceFollowerReplyChronology.referenceDownCut_accepted
    current.output.preparation.coordinator.downView
    (current.output.preparation.followers.followers i).follower
    (current.output.preparation.followers.followers i).row
    (current.output.preparation.followers.followers i).time
    (current.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    logged after raw M scan registers lastService hcurrentAccepted'
  have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
    (current.output.preparation.followers.followers i).follower
    (current.output.preparation.followers.followers i).row
    (current.output.preparation.followers.followers i).activation
    (current.output.preparation.followers.followers i).time
    ((current.output.preparation.followers.followers i).arm,
      current.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    choice logged hlogging
  have hreply : ReferenceFollowerReplyChronology.reply logged =
      ReferenceFollowerReplyChronology.reply choice := by
    simp [ReferenceFollowerReplyChronology.reply, hloggingFrame.1,
      hloggingFrame.2.1, hloggingFrame.2.2.1, hloggingFrame.2.2.2.1]
  have hstartChoice :
      ReferencePrelaunchFollower.acceptedStart choice < s + 1 := by
    have hsame := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
    calc
      ReferencePrelaunchFollower.acceptedStart choice =
          ReferencePrelaunchFollower.acceptedStart logged := hsame.symm
      _ < M.val.sigma := haccepted.1.1
      _ = s + 1 := hcurrentSigma
  obtain ⟨before, beforeMemory, hbeforeInput, hbeforeReply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      current i choice choiceMemory hprepared
  have hpriorFinal : prior.finalState.followers i = .ordinary before beforeMemory := by
    exact hbeforeInput
  have hstartBefore :
      ReferencePrelaunchFollower.acceptedStart before < s + 1 := by
    calc
      ReferencePrelaunchFollower.acceptedStart before =
          ReferencePrelaunchFollower.acceptedStart choice :=
        (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq
          hbeforeReply).symm
      _ < s + 1 := hstartChoice
  intro record hrecord
  obtain ⟨n, hn, hrecordEq⟩ := List.mem_iff_getElem.mp hrecord
  subst record
  intro hreset'
  have hchron := ReferenceFollowerReplyChronology.connected_output_chronology
    prior.connected i before beforeMemory hpriorFinal n hn
  rcases hchron with ⟨next, nextMemory, hnext, hnextBound⟩
  rcases hreset' with ⟨resetCut, hresetDown, resetBefore, resetAfter,
      resetRaw, resetM, resetScan, resetRegisters, resetLastService, hresetAccepted⟩
  obtain ⟨_, _, resetLogged, _, _, _, hresetInput, hresetCut⟩ :=
    actualDownDiagnostic_choice prior.records[n] i resetCut hresetDown
  have hresetAcceptedActual :
      (ReferenceDownReception.referenceDownCut p
        prior.records[n].output.preparation.coordinator.downView
        (prior.records[n].output.preparation.followers.followers i).follower
        (prior.records[n].output.preparation.followers.followers i).row
        (prior.records[n].output.preparation.followers.followers i).time
        (prior.records[n].output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate resetLogged).outcome =
        .accepted resetBefore resetAfter resetRaw resetM resetScan resetRegisters
          resetLastService := by
    rw [← hresetCut]
    exact hresetAccepted
  have hresetBefore : resetBefore = resetLogged :=
    acceptedReferenceCut_before_eq
      prior.records[n].output.preparation.coordinator.downView
      (prior.records[n].output.preparation.followers.followers i).follower
      (prior.records[n].output.preparation.followers.followers i).row
      (prior.records[n].output.preparation.followers.followers i).time
      (prior.records[n].output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      resetLogged resetBefore resetAfter resetRaw resetM resetScan
      resetRegisters resetLastService hresetAcceptedActual
  subst resetBefore
  have happlied : ReferenceFollowerReplyChronology.appliedDown
      prior.records[n] i resetM.val.sigma :=
    ⟨resetLogged, resetCut, resetAfter, resetRaw, resetM, resetScan,
      resetRegisters, resetLastService, hresetInput, hresetDown,
      hresetAccepted, rfl⟩
  obtain ⟨_, _, _, _, hnextStart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict
      prior.records[n] i resetM.val.sigma happlied next nextMemory hnext
  cases hview : prior.records[n].output.preparation.coordinator.downView with
  | none =>
      rw [hview] at hresetAcceptedActual
      rcases acceptedReferenceCut_someView none
        (prior.records[n].output.preparation.followers.followers i).follower
        (prior.records[n].output.preparation.followers.followers i).row
        (prior.records[n].output.preparation.followers.followers i).time
        (prior.records[n].output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        resetLogged resetLogged resetAfter resetRaw resetM resetScan
        resetRegisters resetLastService hresetAcceptedActual with ⟨view, hview⟩
      cases hview
  | some view =>
      have hmem : prior.records[n] ∈ prior.records := List.getElem_mem hn
      have hselectedLower := hwindow prior.records[n] hmem
        view hview
      have hacceptedFields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
        view (prior.records[n].output.preparation.followers.followers i).follower
        (prior.records[n].output.preparation.followers.followers i).row
        (prior.records[n].output.preparation.followers.followers i).time
        (prior.records[n].output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        resetLogged resetLogged resetAfter resetRaw resetM resetScan
        resetRegisters resetLastService (by simpa [hview] using hresetAcceptedActual)
      have hresetSigma : resetM.val.sigma = view.payload.sigma.val + 1 := by
        rw [hacceptedFields.1]
        rw [view.payload.downRecord_fields
          (prior.records[n].output.preparation.followers.followers i).follower]
      have hresetLower : s + 1 ≤ resetM.val.sigma := by
        rw [hresetSigma]
        omega
      omega

/-- The physical list is exactly the records of the canonical run of length
`k+1`; the endpoint is not a separately supplied execution trace. -/
theorem physicalRecords_eq_run_successor (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) :
    physicalRecords initial rows selected rewards s k hspan hmode =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s (k + 1)
        hspan hmode).records := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  rfl

/-- The successor input is the literal next coordinate of the fixed-start
calendar, and the retained physical list has exactly `k+1` entries. -/
theorem physicalRecords_time_and_length (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) :
    (successorRecord initial rows selected rewards s k hspan hmode).input.time.val = s + k ∧
      (physicalRecords initial rows selected rewards s k hspan hmode).length = k + 1 := by
  constructor
  · simp [successorRecord, priorRun, roundInputAt]
  · rw [physicalRecords_eq_run_successor]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
      s (k + 1) hspan hmode

/-- The actual physical input times are exactly the contiguous coordinates
`s, ..., s+k`, including the literal successor. -/
theorem physicalRecords_time_at (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) (j : ℕ)
    (hj : j < (physicalRecords initial rows selected rewards s k hspan hmode).length) :
    ((physicalRecords initial rows selected rewards s k hspan hmode)[j]'hj).input.time.val = s + j := by
  have htimes : (physicalRecords initial rows selected rewards s k hspan hmode).map
        (fun (record : RoundRecord (p := p) (rate := rate)) => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar s (k + 1) := by
        rw [physicalRecords_eq_run_successor]
        exact ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
          s (k + 1) hspan hmode
  have hjtimes : j < ((physicalRecords initial rows selected rewards s k hspan hmode).map
      (fun (record : RoundRecord (p := p) (rate := rate)) =>
        record.input.time.val)).length := by
    simpa using hj
  have hjcalendar : j < (ReferenceActivePhysicalHorizon.calendar s (k + 1)).length := by
    rw [← htimes]
    simpa using hj
  have hindex := congrArg (fun times : List ℕ => times[j]?) htimes
  rw [List.getElem?_eq_getElem hjtimes, List.getElem?_eq_getElem hjcalendar] at hindex
  simp only [List.getElem_map] at hindex
  have hcalendar :
      (ReferenceActivePhysicalHorizon.calendar s (k + 1))[j]'hjcalendar = s + j := by
    simp [ReferenceActivePhysicalHorizon.calendar]
  injection hindex with hvalue
  rw [hcalendar] at hvalue
  exact hvalue

/-- When no actual accepted DOWN reset occurs, the physical fold retains the
whole carried seed and appends every literal per-record emission in order. -/
theorem bufferFold_eq_seed_append_emissions_of_no_reset
    (i : Fin (p.m - 1)) (seed : List (BufferRecord p))
    (records : List (RoundRecord (p := p) (rate := rate)))
    (hreset : ∀ record ∈ records,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record) :
    ReferenceFollowerBufferProvenance.bufferFold i seed records =
      seed ++ records.flatMap (ReferenceFollowerBufferProvenance.logEmission i) := by
  classical
  induction records generalizing seed with
  | nil => simp [ReferenceFollowerBufferProvenance.bufferFold]
  | cons record rest ih =>
      have hrecord := hreset record (by simp)
      have hrest : ∀ next ∈ rest,
          ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i next := by
        intro next hnext
        exact hreset next (by simp [hnext])
      calc
        ReferenceFollowerBufferProvenance.bufferFold i seed (record :: rest) =
            ReferenceFollowerBufferProvenance.bufferFold i
              (seed ++ ReferenceFollowerBufferProvenance.logEmission i record) rest := by
          simp [ReferenceFollowerBufferProvenance.bufferFold,
            ReferenceFollowerBufferProvenance.bufferFoldStep, hrecord]
        _ = (seed ++ ReferenceFollowerBufferProvenance.logEmission i record) ++
              rest.flatMap (ReferenceFollowerBufferProvenance.logEmission i) :=
          ih (seed ++ ReferenceFollowerBufferProvenance.logEmission i record) hrest
        _ = seed ++ (record :: rest).flatMap
              (ReferenceFollowerBufferProvenance.logEmission i) := by
          simp [List.flatMap_cons, List.append_assoc]

/-- A valid accepted successor exposes the exact carried-buffer equation:
actual logging retains the seed once and then all physical emissions from the
canonical prefix and its literal successor. -/
theorem accepted_window_logged_buffer_eq_physical_emissions
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hcurrentInput :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).downInput =
        some logged)
    (hcurrentDown :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).down =
        some cut)
    (hcurrentAccepted :
      cut.outcome = .accepted logged after raw M scan registers lastService)
    (hcurrentSigma : M.val.sigma = s + 1)
    (hwindow : selectedViewInterval s
      (priorRun initial rows selected rewards s k hspan hmode).records) :
    logged.buffer = seed.buffer ++
      (physicalRecords initial rows selected rewards s k hspan hmode).flatMap
        (ReferenceFollowerBufferProvenance.logEmission i) := by
  let prior := priorRun initial rows selected rewards s k hspan hmode
  let current := successorRecord initial rows selected rewards s k hspan hmode
  obtain ⟨choice, choiceMemory, currentLogged, hprepared, hunoccupied,
      hlogging, hdiagInput, _⟩ := actualDownDiagnostic_choice current i cut hcurrentDown
  have hcurrentLogged : currentLogged = logged :=
    Option.some.inj (hdiagInput.symm.trans hcurrentInput)
  subst currentLogged
  have hnoReset := accepted_window_no_prior_reset initial rows selected rewards
    s k hspan hmode i logged cut after raw M scan registers lastService
    hcurrentInput hcurrentDown hcurrentAccepted hcurrentSigma hwindow
  have hlogResult := ReferenceFollowerBufferProvenance.run_logging_ne_error
    i initial rows selected rewards s k hspan hmode seed seedMemory hseed hvalid
    hpair htime choice choiceMemory hprepared hunoccupied
  rcases hlogResult.1 with ⟨actualLogged, hdownInput, hbuffer, _⟩
  have hactualLogged : actualLogged = logged :=
    Option.some.inj (hdownInput.symm.trans hcurrentInput)
  subst actualLogged
  have hfold := bufferFold_eq_seed_append_emissions_of_no_reset i seed.buffer
    prior.records hnoReset
  calc
    logged.buffer =
        ReferenceFollowerBufferProvenance.bufferFold i seed.buffer prior.records ++
          ReferenceFollowerBufferProvenance.logEmission i current := hbuffer
    _ = seed.buffer ++ prior.records.flatMap
          (ReferenceFollowerBufferProvenance.logEmission i) ++
            ReferenceFollowerBufferProvenance.logEmission i current := by rw [hfold]
    _ = seed.buffer ++
          (physicalRecords initial rows selected rewards s k hspan hmode).flatMap
            (ReferenceFollowerBufferProvenance.logEmission i) := by
          simp [physicalRecords, prior, current, List.flatMap_append, List.append_assoc]

/-- The contribution of this follower's literal emission in one actual
record, using the accepted message's arm and exponent. -/
noncomputable def emissionContribution
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (i : Fin (p.m - 1))
    (record : RoundRecord (p := p) (rate := rate)) : ℕ :=
  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
    rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M)
    (record.input.time.val + 1)
    (ReferenceFollowerBufferProvenance.logEmission i record)

/-- A finite contribution fold vanishes when every saved record lies on a
different calendar round. -/
theorem sparseBufferContribution_zero_of_no_matching_round
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (BufferRecord p))
    (hround : ∀ saved ∈ buffer, saved.calendarRound ≠ r) :
    SparseCalendarReplay.sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => simp [SparseCalendarReplay.sparseBufferContribution]
  | cons saved rest ih =>
      have hsaved := hround saved (by simp)
      have hrest : ∀ item ∈ rest, item.calendarRound ≠ r := by
        intro item hitem
        exact hround item (by simp [hitem])
      simp only [SparseCalendarReplay.sparseBufferContribution, List.foldr_cons]
      change (if saved.calendarRound = r ∧ saved.pilot = arm then
          SparseCalendarReplay.savedContribution p.K d D eta h
            saved.observation saved.thinScalar else 0) +
        SparseCalendarReplay.sparseBufferContribution d D eta h arm r rest = 0
      rw [ih hrest]
      simp [hsaved]

/-- Contributions of emissions from source rounds outside the requested
calendar round are zero. The timestamp is taken from each actual record's
literal `logEmission` API. -/
theorem emissionFlatMapContribution_zero_of_source_round_ne
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (i : Fin (p.m - 1)) (r : ℕ)
    (records : List (RoundRecord (p := p) (rate := rate)))
    (hsource : ∀ record ∈ records, record.input.time.val + 1 ≠ r) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
      rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r
      (records.flatMap (ReferenceFollowerBufferProvenance.logEmission i)) = 0 := by
  classical
  induction records with
  | nil => simp [SparseCalendarReplay.sparseBufferContribution]
  | cons record rest ih =>
      have hrecord := hsource record (by simp)
      have hrest : ∀ next ∈ rest, next.input.time.val + 1 ≠ r := by
        intro next hnext
        exact hsource next (by simp [hnext])
      have hsingle : SparseCalendarReplay.sparseBufferContribution (p.m - 1)
          (D p : ℝ) rate.eta.val M.val.h
          (PrelaunchBufferRecovery.downArm rate.eta M) r
          (ReferenceFollowerBufferProvenance.logEmission i record) = 0 := by
        apply sparseBufferContribution_zero_of_no_matching_round
        intro saved hsaved
        have htime := ReferenceFollowerBufferProvenance.logEmission_source_timestamp
          i record saved hsaved
        omega
      rw [List.flatMap_cons,
        SparseCalendarReplay.sparseBufferContribution_append, hsingle, ih hrest]

/-- In a canonical contiguous record list, the sparse-emission contribution
at its nth source round is exactly the contribution of that record's own
literal emission. All earlier and later physical emissions vanish by their
actual one-based source timestamps. -/
theorem emissionFlatMapContribution_getElem
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (i : Fin (p.m - 1)) (start : ℕ)
    (records : List (RoundRecord (p := p) (rate := rate)))
    (n : ℕ) (hn : n < records.length)
    (htimes : ∀ (j : ℕ) (hj : j < records.length),
      (records[j]'hj).input.time.val = start + j) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
      rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M)
      (start + n + 1)
      (records.flatMap (ReferenceFollowerBufferProvenance.logEmission i)) =
    emissionContribution M i records[n] := by
  classical
  induction records generalizing start n with
  | nil => simp at hn
  | cons record rest ih =>
      have hrecordTime : record.input.time.val = start := by
        have hzero : (record :: rest)[0]'(by simp) = record := by simp
        simpa only [hzero, Nat.add_zero] using htimes 0 (by simp)
      have hrestTimes : ∀ (j : ℕ) (hj : j < rest.length),
          (rest[j]'hj).input.time.val = (start + 1) + j := by
        intro j hj
        have h := htimes (j + 1) (by simp [hj])
        have h' : (rest[j]'hj).input.time.val = start + (j + 1) := by
          simpa only [List.getElem_cons_succ] using h
        calc
          (rest[j]'hj).input.time.val = start + (j + 1) := h'
          _ = (start + 1) + j := by omega
      cases n with
      | zero =>
          have htailzero : SparseCalendarReplay.sparseBufferContribution
              (p.m - 1) (D p : ℝ) rate.eta.val M.val.h
              (PrelaunchBufferRecovery.downArm rate.eta M) (start + 1)
              (rest.flatMap (ReferenceFollowerBufferProvenance.logEmission i)) = 0 := by
            apply emissionFlatMapContribution_zero_of_source_round_ne
            intro next hnext
            obtain ⟨j, hj, hnextEq⟩ := List.mem_iff_getElem.mp hnext
            have htime := hrestTimes j hj
            rw [← hnextEq]
            omega
          have hfirst : SparseCalendarReplay.sparseBufferContribution (p.m - 1)
              (D p : ℝ) rate.eta.val M.val.h
              (PrelaunchBufferRecovery.downArm rate.eta M) (start + 1)
              (ReferenceFollowerBufferProvenance.logEmission i record) =
              emissionContribution M i record := by
            simp [emissionContribution, hrecordTime]
          rw [List.flatMap_cons,
            SparseCalendarReplay.sparseBufferContribution_append, hfirst, htailzero]
          simp only [List.getElem_cons_zero, Nat.add_zero]
      | succ n =>
          have hn' : n < rest.length := by simpa using hn
          have hfirstzero : SparseCalendarReplay.sparseBufferContribution
              (p.m - 1) (D p : ℝ) rate.eta.val M.val.h
              (PrelaunchBufferRecovery.downArm rate.eta M) (start + (n + 1) + 1)
              (ReferenceFollowerBufferProvenance.logEmission i record) = 0 := by
            apply sparseBufferContribution_zero_of_no_matching_round
            intro saved hsaved
            have htime := ReferenceFollowerBufferProvenance.logEmission_source_timestamp
              i record saved hsaved
            rw [htime, hrecordTime]
            omega
          have htail := ih (start + 1) n hn' hrestTimes
          rw [List.flatMap_cons,
            SparseCalendarReplay.sparseBufferContribution_append, hfirstzero]
          simp only [List.getElem_cons_succ]
          have hround : start + (n + 1) + 1 = (start + 1) + n + 1 := by omega
          rw [hround]
          simpa using htail

/-- On every accepted scan round, the carried actual buffer contributes
exactly the one actual physical emission from that calendar coordinate.
The endpoint interval, seed bounds, reset exclusion, and actual checked
acceptance are all explicit inputs. -/
theorem accepted_window_bufferArrival_eq_physical_emission
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hcurrentInput :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).downInput =
        some logged)
    (hcurrentDown :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).down =
        some cut)
    (hcurrentAccepted :
      cut.outcome = .accepted logged after raw M scan registers lastService)
    (hcurrentSigma : M.val.sigma = s + 1)
    (hwindow : selectedViewInterval s
      (priorRun initial rows selected rewards s k hspan hmode).records)
    (r : ℕ) (hstart : M.val.sigma ≤ r) (hstop : r < scan.endpoint) :
    ∃ index : Fin ((physicalRecords initial rows selected rewards s k hspan hmode).length),
      index.val = r - M.val.sigma ∧
      ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged r =
        SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
          rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r
          (ReferenceFollowerBufferProvenance.logEmission i
            ((physicalRecords initial rows selected rewards s k hspan hmode).get index)) := by
  let current := successorRecord initial rows selected rewards s k hspan hmode
  let records := physicalRecords initial rows selected rewards s k hspan hmode
  let n := r - M.val.sigma
  have hcurrentTime := (physicalRecords_time_and_length initial rows selected rewards
    s k hspan hmode).1
  have hpreparedTime := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    current.output.preparation i
  have hlocalTime :
      (current.output.preparation.followers.followers i).time = current.input.time := by
    exact hpreparedTime.2.2.1
  have hactualAccepted := actualAcceptedCut_downTransition current i logged cut after raw M
    scan registers lastService hcurrentInput hcurrentDown hcurrentAccepted
  have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
    (current.output.preparation.followers.followers i).follower
    (current.output.preparation.followers.followers i).row
    (current.output.preparation.followers.followers i).time
    (current.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
    registers lastService hactualAccepted
  have hendpoint := hchecked.2.2.2.1
  have hrecordLength := (physicalRecords_time_and_length initial rows selected rewards
    s k hspan hmode).2
  have hendpointBound : scan.endpoint ≤ s + k + 2 := by
    calc
      scan.endpoint ≤
          (current.output.preparation.followers.followers i).time.val + 2 := hendpoint
      _ = current.input.time.val + 2 := by rw [hlocalTime]
      _ = s + k + 2 := by rw [hcurrentTime]
  rw [hcurrentSigma] at hstart
  have hnBound : n < k + 1 := by
    dsimp [n]
    omega
  have hn : n < records.length := by
    change n < (physicalRecords initial rows selected rewards s k hspan hmode).length
    rw [hrecordLength]
    exact hnBound
  have hsourceTime := physicalRecords_time_at initial rows selected rewards
    s k hspan hmode n (by simpa [records] using hn)
  have hseedNoMatch : ∀ saved ∈ seed.buffer, saved.calendarRound ≠ r := by
    intro saved hsaved heq
    have hsavedTime := htime saved hsaved
    omega
  have hseedZero := sparseBufferContribution_zero_of_no_matching_round
    (p.m - 1) (D p : ℝ) rate.eta.val M.val.h
    (PrelaunchBufferRecovery.downArm rate.eta M) r seed.buffer hseedNoMatch
  have hbuffer := accepted_window_logged_buffer_eq_physical_emissions
    initial rows selected rewards s k hspan hmode i seed seedMemory hseed hvalid hpair htime
    logged cut after raw M scan registers lastService hcurrentInput hcurrentDown
    hcurrentAccepted hcurrentSigma hwindow
  have hsourceContribution := emissionFlatMapContribution_getElem M i s records n hn
    (fun j hj => physicalRecords_time_at initial rows selected rewards s k hspan hmode j
      (by simpa [records] using hj))
  have hr : s + n + 1 = r := by
    dsimp [n]
    rw [hcurrentSigma]
    omega
  have hsourceRound : records[n].input.time.val + 1 = r := by
    rw [hsourceTime, hr]
  have hsourceContributionR := hsourceContribution
  rw [hr] at hsourceContributionR
  let index : Fin ((physicalRecords initial rows selected rewards s k hspan hmode).length) :=
    ⟨n, by simpa [records] using hn⟩
  refine ⟨index, ?_, ?_⟩
  · simp [index, n]
  · have hcalc : ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged r =
        SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
          rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r
          (ReferenceFollowerBufferProvenance.logEmission i records[n]) := by
      calc
        ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged r =
            SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r logged.buffer := rfl
        _ = SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r
              (seed.buffer ++ records.flatMap
                (ReferenceFollowerBufferProvenance.logEmission i)) := by rw [hbuffer]
        _ = SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r seed.buffer +
            SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r
              (records.flatMap (ReferenceFollowerBufferProvenance.logEmission i)) :=
          SparseCalendarReplay.sparseBufferContribution_append (p.m - 1) (D p : ℝ)
            rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r seed.buffer _
        _ = emissionContribution M i records[n] := by
          simpa only [hseedZero, zero_add] using hsourceContributionR
        _ = SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r
              (ReferenceFollowerBufferProvenance.logEmission i records[n]) := by
          change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M)
              (records[n].input.time.val + 1)
              (ReferenceFollowerBufferProvenance.logEmission i records[n]) = _
          rw [hsourceRound]
    simpa [List.get, index, records, n] using hcalc

/-- The whole actual accepted calendar input is the enabled image of the
corresponding prefix of the literal physical records. Empty arrivals remain
enabled entries; the initial queue remains the parsed `M.val.q`. -/
theorem accepted_window_recoveryQueueRecords_eq_physical_prefix
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hcurrentInput :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).downInput =
        some logged)
    (hcurrentDown :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).down =
        some cut)
    (hcurrentAccepted :
      cut.outcome = .accepted logged after raw M scan registers lastService)
    (hcurrentSigma : M.val.sigma = s + 1)
    (hwindow : selectedViewInterval s
      (priorRun initial rows selected rewards s k hspan hmode).records) :
    ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged scan.endpoint =
      ((physicalRecords initial rows selected rewards s k hspan hmode).take
        (scan.endpoint - M.val.sigma)).map
          (fun record => (true, emissionContribution M i record)) := by
  let records := physicalRecords initial rows selected rewards s k hspan hmode
  let count := scan.endpoint - M.val.sigma
  let queue := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged scan.endpoint
  let physicalQueue : List (Bool × ℕ) := (records.take count).map
    (fun record => (true, emissionContribution M i record))
  have hcurrentTime := (physicalRecords_time_and_length initial rows selected rewards
    s k hspan hmode).1
  let hcurrent := successorRecord initial rows selected rewards s k hspan hmode
  have hpreparedTime := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    hcurrent.output.preparation i
  have hlocalTime :
      (hcurrent.output.preparation.followers.followers i).time = hcurrent.input.time :=
    hpreparedTime.2.2.1
  have hcurrentTime' : hcurrent.input.time.val = s + k := by
    simpa [hcurrent] using hcurrentTime
  have hactualAccepted := actualAcceptedCut_downTransition hcurrent i logged cut after raw M
    scan registers lastService hcurrentInput hcurrentDown hcurrentAccepted
  have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
    (hcurrent.output.preparation.followers.followers i).follower
    (hcurrent.output.preparation.followers.followers i).row
    (hcurrent.output.preparation.followers.followers i).time
    (hcurrent.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
    registers lastService hactualAccepted
  have hinterval := hchecked.2.2.1
  have hendpoint : scan.endpoint ≤ s + k + 2 := by
    calc
      scan.endpoint ≤
          (hcurrent.output.preparation.followers.followers i).time.val + 2 :=
        hchecked.2.2.2.1
      _ = hcurrent.input.time.val + 2 := by rw [hlocalTime]
      _ = s + k + 2 := by rw [hcurrentTime']
  have hcountBound : count ≤ records.length := by
    change scan.endpoint - M.val.sigma ≤
      (physicalRecords initial rows selected rewards s k hspan hmode).length
    rw [(physicalRecords_time_and_length initial rows selected rewards
      s k hspan hmode).2, hcurrentSigma]
    omega
  have hqueueLength : queue.length = count := by
    simp [queue, count, ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals,
      ActiveFollowerDownAcceptance.recoveryRounds,
      SparseCalendarReplay.sparseCalendarRounds]
  have hphysicalLength : physicalQueue.length = count := by
    simp [physicalQueue, List.length_take, Nat.min_eq_left hcountBound]
  change queue = physicalQueue
  apply List.ext_getElem
  · rw [hqueueLength, hphysicalLength]
  · intro j hjQueue hjPhysical
    have hjcount : j < count := by rw [← hqueueLength]; exact hjQueue
    have hjrecords : j < records.length := lt_of_lt_of_le hjcount hcountBound
    have hleft : queue[j]'hjQueue =
        (true, ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged
          (M.val.sigma + j)) := by
      simp [queue, ActiveFollowerDownAcceptance.recoveryQueueRecords,
        ActiveFollowerDownAcceptance.recoveryArrivals,
        ActiveFollowerDownAcceptance.recoveryRounds,
        SparseCalendarReplay.sparseCalendarRounds, List.getElem_map,
        List.getElem_range]
    have hright : physicalQueue[j]'hjPhysical =
        (true, emissionContribution M i records[j]) := by
      simp [physicalQueue, List.getElem_map, List.getElem_take]
    have hround : M.val.sigma + j = records[j].input.time.val + 1 := by
      have htime := physicalRecords_time_at initial rows selected rewards s k hspan hmode j
        (by simpa [records] using hjrecords)
      rw [hcurrentSigma, htime]
      omega
    have harrival := accepted_window_bufferArrival_eq_physical_emission
      initial rows selected rewards s k hspan hmode i seed seedMemory hseed hvalid hpair htime
      logged cut after raw M scan registers lastService hcurrentInput hcurrentDown
      hcurrentAccepted hcurrentSigma hwindow (M.val.sigma + j) (by omega) (by
        dsimp [count] at hjcount
        omega)
    obtain ⟨index, hindexValue, harrival⟩ := harrival
    have hindexValue' : index.val = j := by
      rw [hindexValue]
      omega
    have hindex : index = ⟨j, by simpa [records] using hjrecords⟩ := Fin.ext hindexValue'
    have harrival' :
        ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged
          (M.val.sigma + j) =
          SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
            rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M)
            (M.val.sigma + j)
            (ReferenceFollowerBufferProvenance.logEmission i records[j]) := by
      simpa [List.get, records, hindex] using harrival
    have hphi : ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged
        (M.val.sigma + j) = emissionContribution M i records[j] := by
      unfold emissionContribution
      rw [← hround]
      exact harrival'
    calc
      queue[j]'hjQueue =
          (true, ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged
            (M.val.sigma + j)) := hleft
      _ = (true, emissionContribution M i records[j]) := by rw [hphi]
      _ = ((records.take count).map
          (fun record => (true, emissionContribution M i record)))[j]'hjPhysical := hright.symm

/-- Accepted local recovery consumes the actual checked operation: returned
registers replay the physical sparse-emission list from the parsed initial
queue, the reported service is the actual final enabled transition, and every
checked prefix remains valid. The raw comparison conclusion is derived from
the accepted cut itself. -/
theorem accepted_window_checked_physical_queue
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s k : ℕ) (hspan : s + (k + 1) ≤ p.T)
    (hmode : allActiveAtStart initial s) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hcurrentInput :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).downInput =
        some logged)
    (hcurrentDown :
      ((successorRecord initial rows selected rewards s k hspan hmode).output.followers i).down =
        some cut)
    (hcurrentAccepted :
      cut.outcome = .accepted logged after raw M scan registers lastService)
    (hcurrentSigma : M.val.sigma = s + 1)
    (hwindow : selectedViewInterval s
      (priorRun initial rows selected rewards s k hspan hmode).records) :
    let physicalInput :=
      ((physicalRecords initial rows selected rewards s k hspan hmode).take
        (scan.endpoint - M.val.sigma)).map
          (fun record => (true, emissionContribution M i record));
    ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
        .ok ⟨registers, lastService⟩ ∧
      registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        physicalInput ∧
      (∀ j, registers = QueueReplay.replay (4 * rate.n)
        (QueueReplay.replay (4 * rate.n) (0, M.val.q) (physicalInput.take j))
          (physicalInput.drop j)) ∧
      registers.1 ≤ p.T * D p ∧ lastService ≤ D p ∧ registers.2 ≤ p.T * D p ∧
      (∃ hinterval : M.val.sigma < scan.endpoint,
        lastService =
          (ActiveFollowerDownAcceptance.recoveredLastTransition p rate M logged
            scan.endpoint hinterval).1 -
          (ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast p rate M logged
            scan.endpoint hinterval).1) ∧
      (∀ j, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩ (physicalInput.take j) = .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          (physicalInput.take j)) ∧
      ¬ ReferenceDownReception.rawMismatch
        (ReferenceDownReception.referenceDownCut p
          ((successorRecord initial rows selected rewards s k hspan hmode).output.preparation.coordinator.downView)
          ((successorRecord initial rows selected rewards s k hspan hmode).output.preparation.followers.followers i).follower
          ((successorRecord initial rows selected rewards s k hspan hmode).output.preparation.followers.followers i).row
          ((successorRecord initial rows selected rewards s k hspan hmode).output.preparation.followers.followers i).time
          ((successorRecord initial rows selected rewards s k hspan hmode).output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged) := by
  let records := physicalRecords initial rows selected rewards s k hspan hmode
  let count := scan.endpoint - M.val.sigma
  let physicalQueue : List (Bool × ℕ) := (records.take count).map
    (fun record => (true, emissionContribution M i record))
  let current := successorRecord initial rows selected rewards s k hspan hmode
  have hactualAccepted := actualAcceptedCut_downTransition current i logged cut after raw M
    scan registers lastService hcurrentInput hcurrentDown hcurrentAccepted
  have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
    (current.output.preparation.followers.followers i).follower
    (current.output.preparation.followers.followers i).row
    (current.output.preparation.followers.followers i).time
    (current.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
    registers lastService hactualAccepted
  have hagreement := ActiveFollowerDownAcceptance.downTransition_accepted_agreement p
    (current.output.preparation.followers.followers i).follower
    (current.output.preparation.followers.followers i).row
    (current.output.preparation.followers.followers i).time
    (current.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
    registers lastService hactualAccepted
  rcases hagreement with ⟨hscoreBound, hserviceBound, hbacklogBound, hregisters, hservice⟩
  obtain ⟨hinterval, _⟩ := hservice
  have hlastService := ActiveFollowerDownAcceptance.checkedRecovery_success_last_service
    p rate M logged scan.endpoint hinterval ⟨registers, lastService⟩ hchecked.2.1
  have hqueue := accepted_window_recoveryQueueRecords_eq_physical_prefix
    initial rows selected rewards s k hspan hmode i seed seedMemory hseed hvalid hpair htime
    logged cut after raw M scan registers lastService hcurrentInput hcurrentDown
    hcurrentAccepted hcurrentSigma hwindow
  have hqueue' :
      ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged scan.endpoint =
        physicalQueue := by
    simpa [physicalQueue, records, count] using hqueue
  have hregistersPhysical : registers =
      QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalQueue := by
    calc
      registers = ActiveFollowerDownAcceptance.recoveredRegisters p rate M logged scan.endpoint :=
        hregisters
      _ = QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalQueue := by
        simp only [ActiveFollowerDownAcceptance.recoveredRegisters]
        rw [hqueue']
  have hsplitReplay : ∀ j, registers =
      QueueReplay.replay (4 * rate.n)
        (QueueReplay.replay (4 * rate.n) (0, M.val.q) (physicalQueue.take j))
        (physicalQueue.drop j) := by
    intro j
    calc
      registers = QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalQueue :=
        hregistersPhysical
      _ = QueueReplay.replay (4 * rate.n)
          (QueueReplay.replay (4 * rate.n) (0, M.val.q) (physicalQueue.take j))
          (physicalQueue.drop j) := by
        simpa only [List.take_append_drop] using
          (QueueReplay.replay_append (4 * rate.n) (0, M.val.q)
            (physicalQueue.take j) (physicalQueue.drop j))
  have hprefix : ∀ j, ∃ middle,
      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
        ⟨(0, M.val.q), 0⟩ (physicalQueue.take j) = .ok middle ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
      middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (physicalQueue.take j) := by
    intro j
    obtain ⟨middle, hcheckedPrefix, hdomain, hprefixRegisters⟩ :=
      ActiveFollowerDownAcceptance.downTransition_accepted_prefix_bounds p
        (current.output.preparation.followers.followers i).follower
        (current.output.preparation.followers.followers i).row
        (current.output.preparation.followers.followers i).time
        (current.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
        registers lastService hactualAccepted j
    have htake := congrArg (fun input : List (Bool × ℕ) => input.take j) hqueue'
    rw [htake] at hcheckedPrefix hprefixRegisters
    exact ⟨middle, hcheckedPrefix, hdomain, hprefixRegisters⟩
  have hnoMismatch := actualAcceptedCut_no_rawMismatch current i logged cut after raw M
    scan registers lastService hcurrentInput hcurrentDown hcurrentAccepted
  refine ⟨hchecked.2.1, ?_, ?_, hscoreBound, hserviceBound, hbacklogBound,
    ⟨hinterval, ?_⟩, ?_, ?_⟩
  · simpa [physicalQueue, records, count] using hregistersPhysical
  · simpa [physicalQueue, records, count] using hsplitReplay
  · simpa [ActiveFollowerDownAcceptance.recoveredLastService] using hlastService
  · refine ?_
    simpa [physicalQueue, records, count] using hprefix
  · simpa [current] using hnoMismatch

/-- The actual launched-boundary replay is the carried chronological seed at
the clipped block stop. Every original launch relation and exclusion binder
from `ofActualLaunchedBoundary` remains visible. -/
theorem actual_launch_seed
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ActualInitializationLaunchState.RateInput p)
    (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (i : Fin (p.m - 1)) :
    ∃ seed memory,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i =
          .ordinary seed memory ∧
      ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ seed.buffer,
        saved.calendarRound ≤ BootstrapObservedFollower.blockStop p
          (ReferenceInitializationRun.nextBlock b h) := by
  exact ReferenceFollowerBufferProvenance.actualLaunchedBoundary_follower_buffer_seed
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
    learnerSeed hlaunched i

/-- Appending a later actual physical suffix continues the same carried seed
through the canonical prefix state. Provenance and chronology apply to the
entire actual run, while `run_append` exposes the exact prefix continuation. -/
theorem actual_suffix_buffer_chronological
    (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hspan : start + (left + right) ≤ p.T)
    (hmode : allActiveAtStart initial start) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (left + right) hspan hmode).finalState.followers i = .ordinary next nextMemory) :
    next.buffer = ReferenceFollowerBufferProvenance.bufferFold i seed.buffer
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (left + right) hspan hmode).records ∧
    ActiveFollowerLifecycle.localBufferValid next ∧
    next.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
    (∀ saved ∈ next.buffer, saved.calendarRound < start + (left + right) + 1) ∧
    ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (left + right) hspan hmode =
      ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
        (start + left) right (by omega) (by omega) hmode
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          left (by omega) hmode) := by
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    left (by omega) hmode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (left + right) hspan hmode
  have hbuffer := ReferenceFollowerBufferProvenance.run_buffer_provenance i initial
    rows selected rewards start (left + right) hspan hmode seed seedMemory hseed hvalid
    hpair htime next nextMemory hnext
  have hchronological := ReferenceFollowerBufferProvenance.run_buffer_chronological i
    initial rows selected rewards start (left + right) hspan hmode seed seedMemory hseed
    hvalid hpair htime next nextMemory hnext
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start left right hspan hmode
  refine ⟨?_, hchronological.1, hchronological.2.1, hchronological.2.2, ?_⟩
  · simpa [full] using hbuffer
  · simpa [prefixRun, full] using happend

end Bandits.Support.ReferenceFollowerSparseEmissionRecovery

end
