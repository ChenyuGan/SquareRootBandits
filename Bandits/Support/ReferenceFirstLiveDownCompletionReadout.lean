/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceReleaseSupport
public import Bandits.Support.ReferenceFirstLiveOverflowMeasurability

/-!
# Retained actual DOWN completion and failure readouts

Sources: `sources/zip4/manuscript/05_binary_transport.tex:7-55,74-124,293-308`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64,141-157`.

These are internal analytic readouts of the existing physical records. A call
must have passed the actual receiver's checks; a hypothetical quota-reaching
bank does not turn a skipped or input-failed operation into a completion.
Completion, solver ambiguity, parsing, ordinary acceptance, reference filtering,
and later recovery failure are distinct. The first-live equivalences produce
the actual first payload, prior unaccepted calls and strict-stamp provenance.
The named next consumer is the exact first-live prior-decoder detector, then
the stopped release endpoint. No decoder tail, all-assignment event equality,
waiting cost, authentic manuscript filtration or main/source closure is asserted.
UP awaiting, second-DOWN ambiguity and numerical-service owners are unchanged.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveDownCompletionReadout

open MeasureTheory
open ConstructorDimensions ReferenceActivePhysicalStep AffineBatchDecoder
open ReferenceFollowerDownDecoderReplay
open ReferenceDownCompletedAmbiguityMeasurability
open scoped Classical

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The original retained physical record. -/
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
/-- Stamped equations, on the original finite calendar and bit width. -/
abbrev Batch (p : ConstructorDimensions.Parameters) := List (AffineBatchDecoder.Entry p.T (width p))

/-- The literal pre-effect bank plus the actual current positive observation. -/
def appendedDownBatch (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta) : Batch p :=
  logged.downBatch.pending ++ positiveAt p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
        (preparedOwnObservation r i) rate logged)) r.input.time

/-- A completion of the actual retained call, even if recovery or finish fails.
Absent, skipped and input-failed operations return honest absence. -/
def completedDownBatch (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) : Option (Batch p) :=
  match (r.output.followers i).downInput, (r.output.followers i).down with
  | some logged, some cut =>
      let B := appendedDownBatch r i logged
      if cut.rawComparison.isSome = true ∧ quota p ≤ B.length then some B else none
  | _, _ => none

/-- Solver multiplicity, independent of raw absence or local acceptance. -/
def multipleSolutions (B : Batch p) : Prop := 1 < (solutions (samples B)).card

/-- This readout excludes every inherited or mixed prelaunch batch by stamps.
It does not define the manuscript's awaited-word event by fiat. -/
def completedAmbiguousAfterStart (s : ℕ) (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) : Prop :=
  ∃ B, completedDownBatch r i = some B ∧
    (∀ e ∈ B, s ≤ e.time.val) ∧ multipleSolutions B

theorem multipleSolutions_iff (B : Batch p) :
    multipleSolutions B ↔ ∃ u v, satisfies (samples B) u ∧
      satisfies (samples B) v ∧ u ≠ v := by
  simp only [multipleSolutions, Finset.one_lt_card_iff, mem_solutions]

theorem completedDownBatch_eq_none_of_no_input (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (h : (r.output.followers i).downInput = none) : completedDownBatch r i = none := by
  simp only [completedDownBatch, h]

theorem completedDownBatch_eq_none_of_no_cut (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (h : (r.output.followers i).down = none) : completedDownBatch r i = none := by
  cases hi : (r.output.followers i).downInput <;> simp only [completedDownBatch, hi, h]

theorem completedDownBatch_eq_some_iff (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) (B : Batch p) :
    completedDownBatch r i = some B ↔
      ∃ logged cut, (r.output.followers i).downInput = some logged ∧
        (r.output.followers i).down = some cut ∧ cut.rawComparison.isSome = true ∧
        quota p ≤ (appendedDownBatch r i logged).length ∧ appendedDownBatch r i logged = B := by
  cases hi : (r.output.followers i).downInput with
  | none => simp only [completedDownBatch, hi, reduceCtorEq, false_iff]; rintro ⟨_, _, h, _⟩; cases h
  | some logged =>
      cases hd : (r.output.followers i).down with
      | none =>
          simp only [completedDownBatch, hi, hd, reduceCtorEq, false_iff]
          rintro ⟨_, _, _, h, _⟩; cases h
      | some cut =>
          simp only [completedDownBatch, hi, hd, Option.some.injEq]
          by_cases h : cut.rawComparison.isSome = true ∧ quota p ≤ (appendedDownBatch r i logged).length
          · simp only [h, and_self, ite_true, Option.some.injEq]
            constructor
            · intro he; exact ⟨logged, cut, rfl, rfl, h.1, h.2, he⟩
            · rintro ⟨l, c, hl, hc, _, _, he⟩
              cases hl; cases hc; exact he
          · simp only [h, ite_false, reduceCtorEq, false_iff]
            rintro ⟨l, c, hl, hc, hcall, hquota, _⟩
            cases hl; cases hc; exact h ⟨hcall, hquota⟩

/-- On retained diagnostics, completion is precisely a passed actual call
whose appended bank reaches quota. Skips and pre-call failures cannot replay. -/
theorem retained_completion_iff (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) :
    (completedDownBatch r i).isSome = true ↔
      cut.rawComparison.isSome = true ∧ quota p ≤ (appendedDownBatch r i logged).length := by
  simp only [completedDownBatch, hi, hd]
  split <;> simp_all only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true, and_self]

theorem completedDownBatch_eq_none_of_not_called (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hn : cut.rawComparison = none) :
    completedDownBatch r i = none := by
  simp only [completedDownBatch, hi, hd, hn, Option.isSome_none, Bool.false_eq_true,
    false_and, ite_false]

/-- Every passed call exposes the actual checked input domains, raw, parse,
acceptance and comparison. There is no successful-output premise. -/
theorem retained_call_fields (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true) :
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
    logged.status = .unoccupied ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
    cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
      (preparedOwnObservation r i) rate logged).2 ∧
    cut.expectedWord = ReferenceDownReception.expectedDownFlatWord
      r.output.preparation.coordinator.downView i r.input.row r.input.time ∧
    cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
    cut.ordinaryAcceptance = ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
      r.input.time logged (ReferenceDownReception.ordinaryParse p rate cut.raw) ∧
    cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) := by
  have he := record_downCut_eq_actual r i logged cut hi hd
  subst cut
  unfold ReferenceDownReception.referenceDownCut at hc ⊢
  split at hc <;> rename_i hselected
  · split at hc <;> rename_i hstatus
    · split at hc <;> rename_i hregisters
      · split at hc <;> rename_i hbatch
        · split at hc <;> rename_i hbuffer
          · simp only [dite_eq_left hselected, dite_eq_left hstatus,
              dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer]
            split <;> rename_i hmatches
            · exact ⟨hselected, hstatus, hregisters, hbatch, hbuffer, rfl, rfl, rfl, rfl,
                by simp only [hmatches, decide_true]⟩
            · exact ⟨hselected, hstatus, hregisters, hbatch, hbuffer, rfl, rfl, rfl, rfl,
                by simp only [hmatches, decide_false]⟩
          · cases hc
        · cases hc
      · cases hc
    · cases hc
  · cases hc

/-- Parse rejection is separate from solver incompleteness and multiplicity. -/
theorem retained_parse_rejection (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true)
    (hparse : cut.ordinaryParse = none) : ¬ cut.ordinaryAcceptance := by
  have hf := retained_call_fields r i logged cut hi hd hc
  rw [hf.2.2.2.2.2.2.2.2.1, ← hf.2.2.2.2.2.2.2.1, hparse]
  exact not_false

/-- A parsed word can fail the ordinary local acceptance test independently
of the reference comparison, solver and subsequent recovery. -/
theorem retained_local_rejection (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparse : cut.ordinaryParse = some M)
    (ha : ¬ OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M) :
    ¬ cut.ordinaryAcceptance := by
  have hf := retained_call_fields r i logged cut hi hd hc
  rw [hf.2.2.2.2.2.2.2.2.1, ← hf.2.2.2.2.2.2.2.1, hparse]
  exact ha

/-- An actual completion has exactly quota entries and the decoder clears and
appends that very batch, regardless of solver, parse, recovery or finish. The
state here is the decoder's pre-effect return, not a fabricated final state. -/
theorem completedDownBatch_spec (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) (B : Batch p)
    (hB : completedDownBatch r i = some B) :
    B.length = quota p ∧ ∃ logged cut,
      (r.output.followers i).downInput = some logged ∧
      (r.output.followers i).down = some cut ∧ cut.rawComparison.isSome = true ∧
      B = appendedDownBatch r i logged ∧
      (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
        (preparedOwnObservation r i) rate logged).1 =
          ⟨[], logged.downBatch.completed ++ [B]⟩ ∧ cut.raw = batchOutput B := by
  obtain ⟨logged, cut, hi, hd, hc, hquota, he⟩ :=
    (completedDownBatch_eq_some_iff r i B).mp hB
  have hf := retained_call_fields r i logged cut hi hd hc
  have hp : logged.downBatch.pending.length < quota p := hf.2.2.2.1.1
  let tr := ActiveFollowerDownAcceptance.currentInputExtension p
    (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
      (preparedOwnObservation r i) rate logged)
  have hlen : (appendedDownBatch r i logged).length ≤ quota p := by
    change (logged.downBatch.pending ++ positiveAt p tr r.input.time).length ≤ quota p
    by_cases h : eligible (tr r.input.time)
    · simp only [positiveAt, ite_eq_left h, List.length_append,
        List.length_singleton]
      omega
    · simp only [positiveAt, ite_eq_right h, List.append_nil]
      exact hp.le
  have heq : (appendedDownBatch r i logged).length = quota p := Nat.le_antisymm hlen hquota
  refine ⟨he ▸ heq, logged, cut, hi, hd, hc, he.symm, ?_, ?_⟩
  · change AffineBatchDecoder.step p tr logged.downBatch r.input.time = _
    have hs : ¬ (logged.downBatch.pending ++ positiveAt p tr r.input.time).length < quota p := by
      change ¬ (appendedDownBatch r i logged).length < quota p
      omega
    simp only [AffineBatchDecoder.step, ite_eq_right hs]
    exact congrArg (fun batch => AffineBatchDecoder.State.mk [] (logged.downBatch.completed ++ [batch])) he
  · rw [hf.2.2.2.2.2.1]
    change stepOutput p tr logged.downBatch r.input.time = _
    have hs : ¬ (logged.downBatch.pending ++ positiveAt p tr r.input.time).length < quota p := by
      change ¬ (appendedDownBatch r i logged).length < quota p
      omega
    simp only [stepOutput, ite_eq_right hs]
    exact congrArg batchOutput he

/-- A passed but incomplete call has no raw output, without calling it ambiguous. -/
theorem retained_incomplete_raw_none (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true)
    (hsmall : (appendedDownBatch r i logged).length < quota p) :
    completedDownBatch r i = none ∧ cut.raw = none := by
  have hf := retained_call_fields r i logged cut hi hd hc
  constructor
  · simp only [completedDownBatch, hi, hd, Nat.not_le_of_lt hsmall, and_false, ite_false]
  · rw [hf.2.2.2.2.2.1]
    exact ite_eq_left hsmall

/-- A completed batch has no raw word exactly when inconsistent or ambiguous.
This explicitly separates two different solver failures. -/
theorem completed_raw_none_iff (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) (B : Batch p)
    (hB : completedDownBatch r i = some B)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hd : (r.output.followers i).down = some cut) :
    cut.raw = none ↔ solutions (samples B) = ∅ ∨ multipleSolutions B := by
  obtain ⟨_, logged, actual, _, ha, _, _, _, hraw⟩ := completedDownBatch_spec r i B hB
  cases ha.symm.trans hd
  rw [hraw]
  rw [multipleSolutions_iff]
  have hempty : solutions (samples B) = ∅ ↔ ∀ u, ¬ satisfies (samples B) u := by
    simp only [Finset.eq_empty_iff_forall_notMem, mem_solutions]
  rw [hempty]
  exact solve_eq_none_iff_empty_or_ambiguous (samples B)

/-- On an actual completed decision, raw presence is precisely unique solvability. -/
theorem completed_raw_some_iff (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) (B : Batch p)
    (hB : completedDownBatch r i = some B)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hd : (r.output.followers i).down = some cut) (w : AffineChannelLaw.Word (width p)) :
    cut.raw = some w ↔ satisfies (samples B) w ∧
      ∀ v, satisfies (samples B) v → v = w := by
  obtain ⟨_, logged, actual, _, ha, _, _, _, hraw⟩ := completedDownBatch_spec r i B hB
  cases ha.symm.trans hd
  rw [hraw]
  exact solve_eq_some_iff (samples B) w

/-- A strict prelaunch entry excludes this stamp-filtered ambiguity test even
when it happens to be solved by the current word. -/
theorem not_completedAmbiguousAfterStart_of_old_entry (s : ℕ) (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (B : Batch p) (hB : completedDownBatch r i = some B)
    (e : AffineBatchDecoder.Entry p.T (width p)) (he : e ∈ B) (hold : e.time.val < s) :
    ¬ completedAmbiguousAfterStart s r i := by
  rintro ⟨B', hB', htimes, _⟩
  have heq : B = B' := Option.some.inj (hB.symm.trans hB')
  subst B'
  exact (Nat.not_le_of_lt hold) (htimes e he)

/-- The logged input originates in the real ordinary unoccupied PREPARE
branch. This inversion uses no successful successor configuration. -/
theorem retained_input_origin (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hi : (r.output.followers i).downInput = some logged) :
    ∃ choice memory,
      (r.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧
      logged.lastDown = choice.lastDown ∧ logged.status = choice.status ∧
      logged.downBatch = choice.downBatch := by
  let prepared := r.output.preparation.followers.followers i
  let own := preparedOwnObservation r i
  let view := r.output.preparation.coordinator.downView
  have hretained : (finishFollower view prepared own).downInput = some logged := by
    rw [← record_preparationDiagnostics r i] at hi
    exact hi
  cases hcfg : prepared.configuration with
  | dagger => simp only [finishFollower, hcfg] at hretained; cases hretained
  | ordinary choice memory =>
      have hf : (finishFollower view prepared own).downInput =
          (recordFollower view prepared.follower prepared.row prepared.activation prepared.time
            prepared.active prepared.arm own choice).downInput := by
        simp only [finishFollower, hcfg]
        cases hr : (recordFollower view prepared.follower prepared.row prepared.activation
            prepared.time prepared.active prepared.arm own choice).result with
        | error failure => rfl
        | ok post =>
            simp only
            cases hout : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
                prepared.row prepared.time own choice memory post with
            | error failure => rfl
            | ok pair => cases pair; rfl
      rw [hf] at hretained
      by_cases hu : choice.status = .unoccupied
      · simp only [recordFollower, dite_eq_left hu] at hretained
        cases hl : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, own) choice with
        | error failure => simp only [hl] at hretained; cases hretained
        | ok post =>
            simp only [hl, Option.some.injEq] at hretained
            subst post
            have hframe := ActiveFollowerLogging.checkedLogging_success_frame _ _ _ _ _ _ _ hl
            exact ⟨choice, memory, rfl, hu, hframe.1, hframe.2.2.2.2.1,
              hframe.2.2.2.2.2.1⟩
      · simp only [recordFollower, dite_eq_right hu] at hretained
        cases hretained

/-- The observation code's actual call agrees with the logged current input,
including the actual feedback, row, sample, time and eligibility bits. -/
theorem retained_call_reconstructs (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hi : (r.output.followers i).downInput = some logged) :
    ∃ call : DownCallCode p,
      downCallObservation i r = some call ∧
      decodeCall call = (r.input.time, ActiveFollowerDownAcceptance.currentRoundInput p i
        r.input.row r.input.time (preparedOwnObservation r i) rate logged) := by
  obtain ⟨choice, memory, hcfg, _, _, hstatus, _⟩ := retained_input_origin r i logged hi
  have hcall := actualDownCall_ordinary r i choice memory hcfg
  have halign := r.output.preparation.follower_alignment i
  have hrow : preparedChoiceRow r i = r.input.row := halign.1
  have htime : preparedChoiceTime r i = r.input.time := halign.2.2.1
  rw [hrow, htime] at hcall
  have hin : ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
      (preparedOwnObservation r i) rate choice =
      ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
        (preparedOwnObservation r i) rate logged := by
    simp only [ActiveFollowerDownAcceptance.currentRoundInput, hstatus]
  rw [hin] at hcall
  have hmap := (downCallObservation_reconstructs i r).trans hcall
  exact Option.map_eq_some_iff.mp hmap

/-- The existing countable diagnostic code reconstructs every failure tag. -/
theorem retained_diagnostics_reconstruct (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    (roundDownObservation r.input i).2.2.2 =
      ((r.output.followers i).downInput.map (FollowerDownMeasurability.followerStateCode rate),
        (r.output.followers i).failure, (r.output.followers i).down.map cutFields) := by
  have h := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r
  have hf := h.2.2.1 i
  change ReferenceFollowerTailComposition.reconstructFollowerObservable
    ((ReferenceActiveStepCompositionMeasurability.wholeStepCode r.input).2.1 i) =
      r.output.followers i at hf
  rw [← hf]
  let output := (ReferenceActiveStepCompositionMeasurability.wholeStepCode r.input).2.1 i
  change diagnosticProjection output =
    ((ReferenceFollowerTailComposition.reconstructFollowerObservable output).downInput.map
      (FollowerDownMeasurability.followerStateCode rate),
      (ReferenceFollowerTailComposition.reconstructFollowerObservable output).failure,
      (ReferenceFollowerTailComposition.reconstructFollowerObservable output).down.map cutFields)
  rcases output with ⟨incoming, failure, input, cut⟩
  cases input with
  | inl absent => rfl
  | inr carry =>
      have hregisters : FollowerDownMeasurability.followerStateCode rate
          (ReferenceFollowerTailComposition.reconstructCarry carry) = carry.1.1 := by
        have hstatus (status : Fin 3) : FollowerDownMeasurability.followerStatusCode
            (FollowerDownMeasurability.followerStatusOfCode status) = status := by
          fin_cases status <;> rfl
        rcases carry with ⟨⟨code, skeleton⟩, values⟩
        cases code
        simp only [ReferenceFollowerTailComposition.reconstructCarry,
          FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
          FollowerDownMeasurability.followerStateOfCode, FollowerDownMeasurability.followerStateCode,
          hstatus, FollowerDownMeasurability.decoderBatchOfCode,
          FollowerDownMeasurability.decoderBatchCode, List.map_map, Function.comp_def,
          FollowerDownMeasurability.decoderEntryCode, FollowerDownMeasurability.decoderEntryOfCode,
          Prod.eta, List.map_id']
      cases cut with
      | none =>
          simp only [diagnosticProjection, ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown, Option.map_some, Option.map_none,
            hregisters]
      | some cut =>
          simp only [diagnosticProjection, ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown, Option.map_some, hregisters]
          congr 2
          simp only [cutCodeFields, cutFields,
            ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode,
            decide_eq_true_eq]
          cases cut.ordinaryAcceptance <;> rfl

/-- Literal finite computation on the existing countable observation. -/
def completedBatchCode (code : DownRoundCode p rate) : Option (Batch p) :=
  match code.2.2.2.1, code.2.2.2.2.2, code.2.2.1 with
  | some logged, some cut, some call =>
      let B := (FollowerDownMeasurability.decoderBatchOfCode logged.downBatch).pending ++
        positiveAt p (ActiveFollowerDownAcceptance.currentInputExtension p (decodeCall call).2) code.1
      if cut.2.2.1.isSome = true ∧ quota p ≤ B.length then some B else none
  | _, _, _ => none

theorem completedBatchCode_actual (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) :
    completedBatchCode (roundDownObservation r.input i) = completedDownBatch r i := by
  have hd := retained_diagnostics_reconstruct r i
  unfold completedBatchCode
  rw [congrArg Prod.fst hd, congrArg (fun z => z.2.2) hd]
  cases hi : (r.output.followers i).downInput with
  | none => simp only [completedDownBatch, hi, Option.map_none]
  | some logged =>
      obtain ⟨call, hcall, hdecode⟩ := retained_call_reconstructs r i logged hi
      have hobs : (roundDownObservation r.input i).2.2.1 = some call := hcall
      cases hc : (r.output.followers i).down with
      | none =>
          simp only [completedDownBatch, hi, hc,
            Option.map_none, Option.map_some]
      | some cut =>
          simp only [completedDownBatch, hi, hc, hobs,
            Option.map_some, hdecode, FollowerDownMeasurability.followerStateCode,
            FollowerDownMeasurability.decoderBatchOfCode_code, cutFields,
            appendedDownBatch]
          rfl

/-- Completion together with every retained local failure and raw diagnostic.
This is a projection of the original record, not another operational state. -/
def downReadout (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) :=
  (completedDownBatch r i,
    (r.output.followers i).downInput.map (FollowerDownMeasurability.followerStateCode rate),
    (r.output.followers i).failure, (r.output.followers i).down.map cutFields)

def observationReadout (code : DownRoundCode p rate) :=
  (completedBatchCode code, code.2.2.2)

theorem observationReadout_actual (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) :
    observationReadout (roundDownObservation r.input i) = downReadout r i := by
  exact congrArg₂ Prod.mk (completedBatchCode_actual r i) (retained_diagnostics_reconstruct r i)

private theorem option_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e := comap_measurable _
  have hs : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hs]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨option_singleton⟩

local instance : MeasurableSingletonClass (FollowerDownMeasurability.FollowerStateCode p rate) :=
  ⟨fun _ => trivial⟩

/-- Every test of completion and the full countable failure diagnostics is
Borel on the original physical input space, without changing its real fibres. -/
theorem measurableSet_downReadout_test (i : Fin (p.m - 1))
    (P : Option (Batch p) × DownDiagnosticCode p rate → Prop) :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      P (downReadout ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ i)} := by
  have hm := (measurable_of_countable (fun code : DownRoundCode p rate =>
    decide (P (observationReadout code)))).comp (measurable_roundDownObservation i)
  have hs := (measurableSet_singleton true).preimage hm
  convert hs using 1
  ext x
  simp only [Function.comp_apply, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq]
  rw [observationReadout_actual ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ i]

/-- The completion flag is a Borel readout, including all no-call branches. -/
theorem measurable_completion_flag (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      (completedDownBatch ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ i).isSome) := by
  apply measurable_to_bool
  exact measurableSet_downReadout_test i (fun data => data.1.isSome = true)

/-- In particular the literal after-start ambiguity test is Borel. -/
theorem measurableSet_completedAmbiguousAfterStart (s : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      completedAmbiguousAfterStart s ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ i} :=
  measurableSet_downReadout_test i (fun data =>
    ∃ B, data.1 = some B ∧ (∀ e ∈ B, s ≤ e.time.val) ∧ multipleSolutions B)

/-- The launch getter used by S and the numerical-window producer are the
same literal corrected source state; only proof terms differ. -/
theorem sourceRun_eq_actualFirstLiveRun
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc
      (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count rfl hspan =
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate source rewards C_star C_h hc count hspan := rfl

/-- This generic equivalence still compares OPTIONS. Actual current-word
presence is an additional conclusion of the first-live producer below. -/
theorem retained_wrongUniqueAccepted_iff (r : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) :
    ReferenceDownReception.wrongUniqueAccepted cut ↔
      ∃ B w, completedDownBatch r i = some B ∧
        satisfies (samples B) w ∧ (∀ v, satisfies (samples B) v → v = w) ∧
        some w ≠ cut.expectedWord ∧
        ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time logged
          (ReferenceDownReception.ordinaryParse p rate (some w)) := by
  constructor
  · intro h
    have hc : cut.rawComparison.isSome = true := by rw [h.1]; rfl
    have hf := retained_call_fields r i logged cut hi hd hc
    obtain ⟨w, hw⟩ : ∃ w, cut.raw = some w := Option.ne_none_iff_exists'.mp h.2.1
    have hs : stepOutput p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
            (preparedOwnObservation r i) rate logged)) logged.downBatch r.input.time = some w :=
      hf.2.2.2.2.2.1.symm.trans hw
    obtain ⟨hq, hsol, huniq⟩ := (stepOutput_eq_some_iff p _ _ _ w).mp hs
    have hB : completedDownBatch r i = some (appendedDownBatch r i logged) :=
      (completedDownBatch_eq_some_iff r i _).mpr ⟨logged, cut, hi, hd, hc, hq, rfl⟩
    refine ⟨appendedDownBatch r i logged, w, hB, hsol, huniq, ?_, ?_⟩
    · have hcomp := hf.2.2.2.2.2.2.2.2.2
      rw [h.1, hw] at hcomp
      have hdFalse : decide (some w = cut.expectedWord) = false := Option.some.inj hcomp.symm
      exact of_decide_eq_false hdFalse
    · rw [← hw, ← hf.2.2.2.2.2.2.2.2.1]
      exact h.2.2
  · rintro ⟨B, w, hB, hsol, huniq, hne, ha⟩
    have hw := (completed_raw_some_iff r i B hB cut hd w).mpr ⟨hsol, huniq⟩
    obtain ⟨l, c, hl, hc, hcalled, _, _⟩ := (completedDownBatch_eq_some_iff r i B).mp hB
    cases hi.symm.trans hl
    cases hd.symm.trans hc
    have hf := retained_call_fields r i logged cut hi hd hcalled
    refine ⟨?_, by rw [hw]; exact Option.some_ne_none w, ?_⟩
    · rw [hf.2.2.2.2.2.2.2.2.2, hw, decide_eq_false hne]
    · rw [hf.2.2.2.2.2.2.2.2.1, hw]
      exact ha

private theorem positive_membership (i : Fin (p.m - 1))
    (records : List (Record (p := p) (rate := rate))) (e : Entry p.T (width p)) :
    e ∈ actualDownPositives i records ↔ ∃ r ∈ records, ∃ call,
      actualDownCall i r = some call ∧
      e ∈ positiveAt p (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
  simp only [actualDownPositives, positiveCallEntries, actualDownCalls,
    List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨call, ⟨r, hr, hc⟩, he⟩
    exact ⟨r, hr, call, hc, he⟩
  · rintro ⟨r, hr, call, hc, he⟩
    exact ⟨call, ⟨r, hr, hc⟩, he⟩

private theorem positive_entry_time (call : Call p) (e : Entry p.T (width p))
    (he : e ∈ positiveAt p (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1) :
    e.time = call.1 := by
  unfold positiveAt at he
  split at he
  · have h := List.mem_singleton.mp he
    exact congrArg Entry.time h
  · cases he

private theorem run_records_take (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s) (b : ℕ) (hb : b ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s b (by omega) active).records =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active).records.take b := by
  obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
    rewards s b (count - b) (by omega) active
  have hp : (ReferenceActivePhysicalHorizon.run initial rows J rewards s b (by omega) active).records.IsPrefix
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active).records :=
    ⟨suffix, by simpa only [Nat.add_sub_of_le hb] using he.symm⟩
  have ht := List.prefix_iff_eq_take.mp hp
  rw [ReferenceActivePhysicalHorizon.run_record_count] at ht
  exact ht

/-- The literal positive feedback in a retained passed DOWN call forces the
actual current affine equation for the actual present sent word. -/
theorem retained_positive_equation (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true)
    (word : AffineChannelLaw.Word (width p))
    (hsent : ReferenceActiveAffinePositiveTest.downSent r.input = some word)
    (hpos : 0 < (preparedOwnObservation r i).val.val) :
    equation (ReferenceDownPhysicalHashRule.originalDownSample r.input) word := by
  have hdown := (retained_call_fields r i logged cut hi hd hc).1
  have hindex : upSenderIndex r.input = i :=
    (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hdown.2
  have hp : ReferenceActiveAffinePositiveTest.downPositive r.input = true := by
    rw [ReferenceActiveAffinePositiveTest.downPositive_eq_diagnostic, hindex]
    change (ReferenceActiveAffinePositiveTest.downDiagnosticCall
      ((ReferenceActivePhysicalStep.step r.input).followers i) &&
      decide (0 < ((prepare r.input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val)) = true
    have hobs : (prepare r.input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) = preparedOwnObservation r i := by
      dsimp only [preparedOwnObservation]
      rw [r.output_eq]
      rfl
    rw [hobs, ← r.output_eq]
    simp only [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hd, hc,
      hpos, decide_true, Bool.true_and]
  rw [equation_iff_affineHash]
  exact ReferenceDownPhysicalHashRule.downPositive_sent_hash_one r.input word hsent hp

private theorem positive_entry_equation (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (l : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some l)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true)
    (word : AffineChannelLaw.Word (width p))
    (hsent : ReferenceActiveAffinePositiveTest.downSent r.input = some word)
    (call : Call p) (hcall : actualDownCall i r = some call) (e : Entry p.T (width p))
    (he : e ∈ positiveAt p (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1) :
    equation e.sample word := by
  have hel : eligible call.2 := by
    by_contra hn
    simp only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hn, ite_false, List.not_mem_nil] at he
  have heq : e = entry p (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
    simpa only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hel, ite_true, List.mem_singleton] using he
  have hsample := actualDownCall_sample_original_of_eligible r i call hcall hel
  obtain ⟨code, hcode, hdecode⟩ := retained_call_reconstructs r i l hi
  have hactual : actualDownCall i r = some (r.input.time,
      ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
        (preparedOwnObservation r i) rate l) := by
    rw [← downCallObservation_reconstructs i r, hcode, Option.map_some, hdecode]
  have hcEq := Option.some.inj (hcall.symm.trans hactual)
  have hpos : 0 < (preparedOwnObservation r i).val.val := by
    rw [hcEq] at hel
    exact hel.2.2
  rw [heq]
  change equation call.2.sample word
  rw [hsample]
  exact retained_positive_equation r i l cut hi hd hc word hsent hpos

section ActualFirstLive

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)

/-- Corrected launch produces the actual carried bank's size, chronology and
STRICT pre-offset stamps, as well as no earlier accepted assignment. -/
theorem actual_corrected_decoder_seed :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc
    ∀ i, ∃ state memory, initial.followers i = .ordinary state memory ∧
      state.lastDown = none ∧ state.status = .unoccupied ∧
      ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch ∧
      ReferenceFollowerDecoderChronology.downCollectedChronological state.downBatch ∧
      ∀ e ∈ collected state.downBatch, e.time.val < s := by
  intro s initial i
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  obtain ⟨active, hactive, hbatch⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed rate source rewards C_star C_h hc
  have heq : active = initial := Option.some.inj
    (hactive.symm.trans (ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hc))
  subst active
  obtain ⟨st, mem, hs, hu, hb, hchron, hstamp⟩ := hbatch i
  have hnone : st.lastDown = none := by
    have he : st = seed.followers i := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hs.symm.trans (seed.configuration i))).1
    rw [he]
    exact seed.lastDown_none i
  exact ⟨st, mem, hs, hnone, hu, hb, hchron, hstamp⟩

/-- Recover the PREVIOUS actual unaccepted boundary from PREPARE. It imposes
no ordinary endpoint after the current detecting call. -/
theorem actual_first_live_unaccepted_boundary :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta),
      (W[k.val].output.followers i).downInput = some logged →
      ∃ (hprefix : s + k.val ≤ p.T) (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceActivePhysicalHorizon.run
          (ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k.val hprefix
          (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc).activeAtStart
        ).finalState.followers i = .ordinary before memory ∧
        W[k.val].input.state.followers i = .ordinary before memory ∧
        (W[k.val].output.preparation.followers.followers i).configuration = .ordinary before memory ∧
        before.status = .unoccupied ∧ before.lastDown = none ∧
        logged.lastDown = none ∧ logged.downBatch = before.downBatch := by
  intro s R W k i logged hi
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let r := W[k.val]
  obtain ⟨choice, choiceMemory, hchoice, hcu, hlast, _, hbatch⟩ := retained_input_origin r i logged hi
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero seed.backlog_zero
    seed.lastDown_none seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  obtain ⟨hprefix, hstates⟩ := hsafe.1 k.val k.isLt.le
  obtain ⟨before, memory, hbefore, hlocal, _, _, _, hzero, hoccupied⟩ := hstates i
  obtain ⟨hstep, hactual, _⟩ := ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
    initial source.1.2 J rewards s count hspan seed.activeAtStart k
  have hinput : r.input.state = (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards
      s k.val hprefix seed.activeAtStart).finalState :=
    congrArg (fun rec : Record (p := p) (rate := rate) => rec.input.state) hactual
  have hbconfig : r.input.state.followers i = .ordinary before memory := by rw [hinput]; exact hbefore
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k
  obtain ⟨hsigma, htime, hgrid, hbits⟩ := ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst k cell.selected cell.selection_actual
  change r.input.time.val = s + k.val at htime
  change ∀ t : Fin p.T, s ≤ t.val → t.val < r.input.time.val →
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J) t = false at hbits
  have hprepared := hchoice
  rw [r.output.preparation.followers.followers_eq i] at hprepared
  change (DeclaredFollowerLocalRound.prepare rate i r.input.row (r.input.state.activations i)
    r.input.time (r.input.active i) (r.input.state.followers i)).configuration = _ at hprepared
  rw [hbconfig] at hprepared
  obtain ⟨bb, mm, hbb, hstartActual, _, _⟩ := ReferenceFollowerReplyChronology.prepare_ordinary_inversion
    i r.input.row (r.input.state.activations i) r.input.time (r.input.active i)
    (.ordinary before memory) choice choiceMemory hprepared
  cases hbb
  have hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time before memory = .ok (before, memory) := by
    by_cases hu : before.status = .unoccupied
    · exact ActiveFollowerLifecycle.startRound_unoccupied rate.eta r.input.time before memory hlocal hu
    · obtain ⟨hkpos, M, token, hM, hMsigma, hread, hstamp, hbit⟩ := hoccupied hu
      have hcoord : ActiveFollowerLifecycle.acceptedStartCoordinate M = cell.selected.view.payload.sigma := by
        apply Fin.ext
        have hh := ActiveFollowerLifecycle.accepted_start_coordinate_one_based M
        omega
      have htimeM : M.val.sigma ≤ r.input.time.val := by omega
      have hgridM : r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by rw [hcoord]; exact hgrid
      have hbitFalse : token.bit = false := by
        rw [hbit]
        apply hbits token.timestamp <;> omega
      have hgridNe : FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerLifecycle.acceptedStartCoordinate M) ≠ r.input.time.val + 1 := by omega
      have hbranch := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta r.input.time before memory
        hu hlocal M hM htimeM (by omega) token hread
        (by change token.timestamp.val + 1 = r.input.time.val; omega)
      simpa only [hgridNe, decide_false, hbitFalse, Bool.false_or,
        Bool.false_eq_true, ite_false] using hbranch
  have heq : before = choice ∧ memory = choiceMemory := Prod.mk.inj (Except.ok.inj (hstart.symm.trans hstartActual))
  rcases heq with ⟨rfl, rfl⟩
  exact ⟨hprefix, before, memory, hbefore, hbconfig, hchoice, hcu, (hzero hcu).1,
    hlast.trans (hzero hcu).1, hbatch⟩

/-- A launch-time installation witness in this same source run is at its real
FIRST coordinator state, rather than an earlier or later assignment. -/
theorem actual_first_live_birth_first :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    ∀ birth ∈ R.records, birth.input.time.val = s → birth.input.state.coordinator = .first := by
  intro s R birth hbirth htime
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  obtain ⟨a, _, hta, hstate⟩ := ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    s count hspan seed.activeAtStart birth hbirth
  have ha : a = 0 := by omega
  subst a
  have hzero := ReferenceActivePhysicalHorizon.run_zero_final initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (by omega) seed.activeAtStart
  have hstate0 : birth.input.state = initial := hstate.trans hzero
  exact (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator) hstate0).trans
    seed.coordinatorFirst

/-- The actual current first DOWN word is PRESENT. Its payload was installed
at this launch, and it passes the ordinary local acceptance test. Option
mismatch with an absent expected word is therefore excluded on this domain. -/
theorem actual_first_live_current_word :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      (W[k.val].output.followers i).downInput = some logged →
      (W[k.val].output.followers i).down = some cut → cut.rawComparison.isSome = true →
      ∃ (selected : ReferenceActivePhysicalStep.Selection W[k.val].input) (birth : Record (p := p) (rate := rate)),
        W[k.val].output.preparation.coordinator.selection = some selected ∧
        birth ∈ R.records ∧ birth.input.time.val = s ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth selected.view.payload ∧
        selected.view.payload.sigma.val = s ∧ i ∈ selected.view.pendingAtChoice ∧
        cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) ∧
        ReferenceActiveAffinePositiveTest.downSent W[k.val].input =
          some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) ∧
        ReferenceDownReception.ordinaryParse p rate
          (some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i)) =
            some (selected.view.payload.downRecord i) ∧
        OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (ReferencePrelaunchFollower.acceptedStart logged) (W[k.val].input.time.val + 1)
          (selected.view.payload.downRecord i) := by
  intro s R W k i logged cut hi hd hcalled
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let r := W[k.val]
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan k
  let selected := cell.selected
  have hselected : r.output.preparation.coordinator.selection = some selected := cell.selection_actual
  obtain ⟨hprefix, before, memory, hbefore, hbinput, hbchoice, hbu, hbn, hln, _⟩ :=
    actual_first_live_unaccepted_boundary rate source rewards C_star C_h count hc hspan k i logged hi
  have hf := retained_call_fields r i logged cut hi hd hcalled
  have hdown := hf.1
  have hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro j st mem hst
    have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((seed.configuration j).symm.trans hst)
    rcases he with ⟨rfl, rfl⟩
    exact ⟨seed.unoccupied j, seed.lastDown_none j⟩
  have hpref : W.IsPrefix R.records := List.takeWhile_prefix _
  have hpending : i ∈ selected.view.pendingAtChoice := by
    by_contra hn
    have hprov := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
      initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst
    rcases hprov with hz | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrows⟩
    · change W.length = 0 at hz
      have hh : k.val < W.length := k.isLt
      omega
    · obtain ⟨rr, hrr, ss, hss, _, _, nx, ow, bs, _, _, _, hcoverage⟩ := hrows k
      cases hrr
      have he : ss = selected := Option.some.inj (hss.symm.trans hselected)
      subst ss
      obtain ⟨ell, hell, prior, hprior, priorSelected, hpsel, _, hevent, hindex⟩ := hcoverage i hn
      cases hprior
      have hellW : ell < W.length := hell.trans k.isLt
      change W[ell].output.preparation.coordinator.selection = some priorSelected at hpsel
      change ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[ell] priorSelected at hevent
      change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[ell].input.row.2 W[ell].input.time).1 = i at hindex
      let ellFin : Fin W.length := ⟨ell, hellW⟩
      let priorCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate source rewards C_star C_h hc count hspan ellFin
      have hselected' : (prepare W[ell].input).coordinator.selection = some priorSelected := by
        simpa only [W[ell].output_eq, ReferenceActivePhysicalStep.step] using hpsel
      have hchoice' : ((prepare W[ell].input).followers.followers
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (W[ell].input.row.2 W[ell].input.time).1)).configuration =
            .ordinary (priorCell.states i) (priorCell.memories i) := by
        rw [hindex]
        have hco : (W[ell].output.preparation.followers.followers i).configuration =
            .ordinary (priorCell.states i) (priorCell.memories i) := priorCell.ordinary i
        simpa only [W[ell].output_eq, ReferenceActivePhysicalStep.step] using hco
      have hocc := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
        (prepare W[ell].input) priorSelected hselected' (priorCell.states i)
        (priorCell.memories i) hchoice' (by
          simpa only [W[ell].output_eq, ReferenceActivePhysicalStep.step,
            ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent] using hevent)
      have hne : (priorCell.states i).status ≠ .unoccupied := by
        rcases hocc with h | h <;> rw [h] <;> decide
      have hlast := ReferenceFirstLiveUnoccupiedEmission.actual_retained_down_fields
        rate source rewards C_star C_h hc count hspan ellFin i hne
      have hpos : 1 ≤ ReferencePrelaunchFollower.acceptedStart (priorCell.states i) := by
        rw [ReferencePrelaunchFollower.acceptedStart, hlast]
        exact (priorCell.selected.view.payload.downRecord i).property.1
      have hellR : ell < R.records.length := hellW.trans_le hpref.length_le
      have hkR : k.val < R.records.length := k.isLt.trans_le hpref.length_le
      have hl : (ReferenceFollowerFixedReply.actualChoice R.records[ell] i).configuration =
          .ordinary (priorCell.states i) (priorCell.memories i) := by
        change (R.records[ell].output.preparation.followers.followers i).configuration = _
        rw [← hpref.getElem hellW]
        exact priorCell.ordinary i
      have hr : (ReferenceFollowerFixedReply.actualChoice R.records[k.val] i).configuration =
          .ordinary before memory := by
        change (R.records[k.val].output.preparation.followers.followers i).configuration = _
        rw [← hpref.getElem k.isLt]
        exact hbchoice
      have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology R.connected i
        ell k.val hellR hkR (by omega) (priorCell.states i) before
        (priorCell.memories i) memory hl hr).1
      have hz : ReferencePrelaunchFollower.acceptedStart before = 0 := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hbn]
      omega
  obtain ⟨birth, hbirth, hbirthTime, hborn, hsigma, _⟩ :=
    ReferenceFirstDownRecoveryBudget.run_first_selected_payload initial source.1.2 J rewards
      s count hspan seed.activeAtStart seed.coordinatorFirst k selected hselected
  have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i r.input.row r.input.time :=
    ⟨hdown.1, hdown.2, hpending⟩
  have hexpected := selected.expected_down_word i hbranch
  have hview : r.output.preparation.coordinator.downView = some selected.view := by
    change r.output.preparation.coordinator.selection.map Selection.view = _
    rw [hselected]; rfl
  have hcutWord : cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) := by
    rw [hf.2.2.2.2.2.2.1, hview]
    exact hexpected
  have hindex : upSenderIndex r.input = i :=
    (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hdown.2
  have hsent : ReferenceActiveAffinePositiveTest.downSent r.input =
      some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) := by
    unfold ReferenceActiveAffinePositiveTest.downSent
    rw [hindex]
    have hv : (dispatch r.input).downView = some selected.view := by
      rw [← r.output.preparation.coordinator_eq]
      exact hview
    rw [hv]
    exact hexpected
  have hparse : ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i)) =
        some (selected.view.payload.downRecord i) := by
    change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
        ((OrdinaryMessageCodec.wordEquivFlat _) (selected.view.payload.downWord i)))) = _
    rw [Equiv.symm_apply_apply, selected.view.payload.parseDown_downWord i]
  have htime := (ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst k selected hselected).2.1
  have haccept : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1)
      (selected.view.payload.downRecord i) := by
    constructor
    · change ReferencePrelaunchFollower.acceptedStart logged < selected.view.payload.sigma.val + 1
      simp only [ReferencePrelaunchFollower.acceptedStart, hln]
      omega
    · change selected.view.payload.sigma.val + 1 ≤ r.input.time.val + 1
      change r.input.time.val = s + k.val at htime
      omega
  exact ⟨selected, birth, hselected, hbirth, hbirthTime, hborn, hsigma, hpending,
    hcutWord, hsent, hparse, haccept⟩

/-- Every selected DOWN in the actual still-unaccepted interval, including
its detecting call, sends the SAME first payload and passes ordinary local
acceptance. All prior call obligations come from the public unaccepted-epoch
producer at the previous boundary; zero has no previous interval. -/
theorem actual_first_live_awaited_calls :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      (W[k.val].output.followers i).downInput = some logged →
      (W[k.val].output.followers i).down = some cut → cut.rawComparison.isSome = true →
      ∃ (M : Payload rate) (birth : Record (p := p) (rate := rate)),
        M.sigma.val = s ∧ birth ∈ R.records ∧ birth.input.time.val = s ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth M ∧
        cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
        ∀ record ∈ R.records.take (k.val + 1),
          ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
          ∃ l c, (record.output.followers i).downInput = some l ∧
            (record.output.followers i).down = some c ∧ c.rawComparison.isSome = true ∧
            c.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
            ReferenceActiveAffinePositiveTest.downSent record.input =
              some (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
            ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time l
              (ReferenceDownReception.ordinaryParse p rate
                (some (CoordinatorLocalArmChoice.storedDownFlatWord M i))) ∧
            (0 < (preparedOwnObservation record i).val.val →
              equation (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                (CoordinatorLocalArmChoice.storedDownFlatWord M i)) := by
  intro s R W k i logged cut hi hd hcalled
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let r := W[k.val]
  obtain ⟨selected, birth, hselected, hbirth, hbirthTime, hborn, hsigma,
    _, hword, hsent, hparse, haccept⟩ :=
    actual_first_live_current_word rate source rewards C_star C_h count hc hspan k i logged cut hi hd hcalled
  refine ⟨selected.view.payload, birth, hsigma, hbirth, hbirthTime, hborn, hword, ?_⟩
  intro record hrecord hdown
  have hpref : W.IsPrefix R.records := List.takeWhile_prefix _
  have hkR : k.val < R.records.length := k.isLt.trans_le hpref.length_le
  rw [List.take_succ_eq_append_getElem hkR, List.mem_append, List.mem_singleton] at hrecord
  rcases hrecord with hprevious | hcurrent
  · have hkpos : 0 < k.val := by
      by_contra hn
      have hz : k.val = 0 := by omega
      simp only [hz, List.take_zero, List.not_mem_nil] at hprevious
    obtain ⟨hprefix, before, memory, hbefore, hbinput, _, _, hnone, _, _⟩ :=
      actual_first_live_unaccepted_boundary rate source rewards C_star C_h count hc hspan k i logged hi
    have hcoordSafe := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
      initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst
    obtain ⟨regs, owned, base, hcoord⟩ := (hcoordSafe.2.1 k.val k.isLt.le).2 hkpos
    have hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
      intro j st mem hst
      have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        ((seed.configuration j).symm.trans hst)
      rcases he with ⟨rfl, rfl⟩
      exact ⟨seed.unoccupied j, seed.lastDown_none j⟩
    have hcount : k.val ≤ count := by
      have hh := hpref.length_le
      have hl : R.records.length = count := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
      omega
    have hprov := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
      initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst
    rcases hprov with hz | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrows⟩
    · change W.length = 0 at hz
      have hh : k.val < W.length := k.isLt
      omega
    · obtain ⟨rr, hrr, ss, hss, _, hphase, _⟩ := hrows k
      cases hrr
      have he : ss = selected := Option.some.inj (hss.symm.trans hselected)
      subst ss
      obtain ⟨_, hactual, _⟩ := ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
        initial source.1.2 J rewards s count hspan seed.activeAtStart k
      have hstate : r.input.state = (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards
          s k.val hprefix seed.activeAtStart).finalState := congrArg (fun rr : Record (p := p) (rate := rate) => rr.input.state) hactual
      have hic : r.input.state.coordinator = .live regs owned base := by rw [hstate]; exact hcoord
      change (match r.input.state.coordinator with
        | .first => _ | .live incoming _ _ => _ | _ => _) at hphase
      rw [hic] at hphase
      have hpayload : selected.view.payload = regs.payload := hphase.1
      have hepoch := ReferenceFirstUnacceptedDownEpoch.run_first_unaccepted_down_epoch
        initial source.1.2 J rewards s count hspan seed.activeAtStart seed.coordinatorFirst hseed
        k.val hcount k.isLt.le regs owned base hcoord i before memory hbefore hnone
      obtain ⟨a, ha, sel, bs, bm, choice, cm, next, nm, htime, hinput, hrowsEq, hJ, hrewards,
        hsel, hpay, hpend, hstarted, hbs, hch, hn, hbn, hcn, hnn, hbu, hcu, hnu, hcall⟩ :=
        hepoch.2 record hprevious
      obtain ⟨l, hlog, hli, hci, hln, hlu, hbank, hsend, hexpected, hcw, hparsed,
        haccepted, hreg, hdec, hbuf, hcomp, hraw, hnext, hround, hsample, hre, hpt, hentry, hhash⟩ := hcall hdown
      refine ⟨l, _, hli, hci, hcomp, ?_, ?_, ?_, ?_⟩
      · simpa only [← hpayload] using hcw
      · simpa only [← hpayload] using hsend
      · rw [hpayload, hparsed]
        exact haccepted
      · intro hp
        rw [hpayload]
        exact (AffineBatchDecoder.equation_iff_affineHash _ _).mpr (hhash hp)
  · have he : record = r := hcurrent.trans (hpref.getElem k.isLt).symm
    rw [he]
    refine ⟨logged, cut, hi, hd, hcalled, hword, hsent, ?_, ?_⟩
    · rw [hparse]
      exact haccept
    · exact retained_positive_equation r i logged cut hi hd hcalled _ hsent

/-- An entry of the actual completed bank is postlaunch EXACTLY when it came
from this actual run's positive calls through the detecting call. The carried
prelaunch bank is preserved, then excluded by its strict stamps. -/
theorem actual_first_live_batch_origins :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1)) (B : Batch p),
      completedDownBatch W[k.val] i = some B →
      ∀ e ∈ B, s ≤ e.time.val ↔ e ∈ actualDownPositives i (R.records.take (k.val + 1)) := by
  intro s R W k i B hB
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let r := W[k.val]
  obtain ⟨logged, cut, hi, hd, hcalled, _, heB⟩ := (completedDownBatch_eq_some_iff r i B).mp hB
  obtain ⟨hprefix, before, memory, hbefore, _, _, _, _, _, hbank⟩ :=
    actual_first_live_unaccepted_boundary rate source rewards C_star C_h count hc hspan k i logged hi
  obtain ⟨active, hactive, hseed⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed rate source rewards C_star C_h hc
  have heq : active = initial := Option.some.inj (hactive.symm.trans
    (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate source rewards C_star C_h hc))
  subst active
  have hreplay := run_downBatch_replay initial source.1.2 J rewards s k.val hprefix seed.activeAtStart
    hseed i (seed.followers i) (seed.memory i) (seed.configuration i) before memory hbefore
  have hpref : W.IsPrefix R.records := List.takeWhile_prefix _
  have hkR : k.val < R.records.length := k.isLt.trans_le hpref.length_le
  have hkcount : k.val ≤ count := by
    have hh := hpref.length_le
    have hl : R.records.length = count := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    omega
  have htake := run_records_take initial source.1.2 J rewards s count hspan seed.activeAtStart k.val hkcount
  let call : Call p := (r.input.time, ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
    r.input.time (preparedOwnObservation r i) rate logged)
  have hcall : actualDownCall i r = some call := by
    obtain ⟨code, hcode, hdecode⟩ := retained_call_reconstructs r i logged hi
    rw [← downCallObservation_reconstructs i r, hcode, Option.map_some, hdecode]
  change actualDownCall i W[k.val] = some call at hcall
  have hpositives : actualDownPositives i (R.records.take (k.val + 1)) =
      actualDownPositives i (R.records.take k.val) ++
        positiveAt p (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
    rw [List.take_succ_eq_append_getElem hkR, ← hpref.getElem k.isLt]
    simp only [actualDownPositives, actualDownCalls, List.filterMap_append,
      List.filterMap_cons, hcall, List.filterMap_nil, positiveCallEntries,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s k.val hprefix
    seed.activeAtStart).records = R.records.take k.val at htake
  have hcollected : collected before.downBatch = collected (seed.followers i).downBatch ++
      actualDownPositives i (R.records.take k.val) := by
    rw [← htake]
    exact hreplay.2.1
  have hseedStamps : ∀ e ∈ collected (seed.followers i).downBatch, e.time.val < s := by
    obtain ⟨st, mem, hst, _, _, _, hstamp⟩ := hseed i
    have he : st = seed.followers i := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hst.symm.trans (seed.configuration i))).1
    rw [← he]
    exact hstamp
  intro e he
  constructor
  · intro htime
    rw [← heB, appendedDownBatch, hbank] at he
    rcases List.mem_append.mp he with hold | hcurrent
    · have hmem : e ∈ collected before.downBatch := List.mem_append_right _ hold
      rw [hcollected, List.mem_append] at hmem
      rcases hmem with hseedOld | hnew
      · exact False.elim ((Nat.not_le_of_lt (hseedStamps e hseedOld)) htime)
      · rw [hpositives]
        exact List.mem_append_left _ hnew
    · rw [hpositives]
      exact List.mem_append_right _ hcurrent
  · intro hpos
    obtain ⟨record, hrecord, c, hcActual, he⟩ := (positive_membership i _ e).mp hpos
    have hcFields := actualDownCall_fields record i c hcActual
    have heTime := positive_entry_time c e he
    have hm : record ∈ R.records := List.mem_of_mem_take hrecord
    obtain ⟨a, _, htime, _⟩ := ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
      initial source.1.2 J rewards s count hspan seed.activeAtStart record hm
    rw [heTime, hcFields.1, htime]
    exact Nat.le_add_right _ _

/-- Substantive first-assignment ambiguity characterization. The right side
exhibits the first installed payload, actual receiver calls and ordinary local
acceptance throughout its unaccepted interval, and actual postlaunch origins
for EVERY equation. It is not an equality with a source-wide failure event. -/
theorem actual_first_live_completedAmbiguousAfterStart_iff :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1)),
      completedAmbiguousAfterStart s W[k.val] i ↔
      ∃ (M : Payload rate) (birth : Record (p := p) (rate := rate)) (B : Batch p),
        M.sigma.val = s ∧ birth ∈ R.records ∧ birth.input.time.val = s ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth M ∧
        birth.input.state.coordinator = .first ∧
        completedDownBatch W[k.val] i = some B ∧
        (∀ e ∈ B, e ∈ actualDownPositives i (R.records.take (k.val + 1))) ∧
        satisfies (samples B) (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
        (∃ u v, satisfies (samples B) u ∧ satisfies (samples B) v ∧ u ≠ v) ∧
        ∀ record ∈ R.records.take (k.val + 1),
          ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
          ∃ l c, (record.output.followers i).downInput = some l ∧
            (record.output.followers i).down = some c ∧ c.rawComparison.isSome = true ∧
            c.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
            ReferenceActiveAffinePositiveTest.downSent record.input =
              some (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
            ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time l
              (ReferenceDownReception.ordinaryParse p rate
                (some (CoordinatorLocalArmChoice.storedDownFlatWord M i))) ∧
            (0 < (preparedOwnObservation record i).val.val →
              equation (ReferenceDownPhysicalHashRule.originalDownSample record.input)
                (CoordinatorLocalArmChoice.storedDownFlatWord M i)) := by
  intro s R W k i
  constructor
  · rintro ⟨B, hB, htimes, hmulti⟩
    obtain ⟨logged, cut, hi, hd, hcalled, _, _⟩ := (completedDownBatch_eq_some_iff W[k.val] i B).mp hB
    obtain ⟨M, birth, hsigma, hbirth, htime, hborn, _, hcalls⟩ :=
      actual_first_live_awaited_calls rate source rewards C_star C_h count hc hspan k i logged cut hi hd hcalled
    have horig : ∀ e ∈ B, e ∈ actualDownPositives i (R.records.take (k.val + 1)) := by
      intro e he
      exact (actual_first_live_batch_origins rate source rewards C_star C_h count hc hspan k i B hB e he).mp
        (htimes e he)
    refine ⟨M, birth, B, hsigma, hbirth, htime, hborn,
      actual_first_live_birth_first rate source rewards C_star C_h count hc hspan birth hbirth htime,
      hB, horig, ?_,
      (multipleSolutions_iff B).mp hmulti, hcalls⟩
    apply (satisfies_samples_iff B _).mpr
    intro e he
    obtain ⟨record, hrecord, call, hcActual, hePos⟩ := (positive_membership i _ e).mp (horig e he)
    have hel : eligible call.2 := by
      by_contra hn
      simp only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
        hn, ite_false, List.not_mem_nil] at hePos
    have hdown := (actualDownCall_fields record i call hcActual).2.2.mp hel.1
    obtain ⟨l, c, hi, hd, hcomp, _, hsent, _, _⟩ := hcalls record hrecord hdown
    exact positive_entry_equation record i l c hi hd hcomp _ hsent call hcActual e hePos
  · rintro ⟨M, birth, B, _, _, _, _, _, hB, horig, _, hmulti, _⟩
    refine ⟨B, hB, ?_, (multipleSolutions_iff B).mpr hmulti⟩
    intro e he
    exact (actual_first_live_batch_origins rate source rewards C_star C_h count hc hspan k i B hB e he).mpr
      (horig e he)

/-- On the same actual first-live domain, a wrong unique accepted word is
DIFFERENT FROM A PRESENT current first payload word, not merely from `none`. -/
theorem actual_first_live_wrongUniqueAccepted_iff :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h hc s count rfl hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      (W[k.val].output.followers i).downInput = some logged →
      (W[k.val].output.followers i).down = some cut →
      (ReferenceDownReception.wrongUniqueAccepted cut ↔
        ∃ (M : Payload rate) (birth : Record (p := p) (rate := rate)) (B : Batch p)
          (w : AffineChannelLaw.Word (width p)),
          M.sigma.val = s ∧ birth ∈ R.records ∧ birth.input.time.val = s ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth birth M ∧
          cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord M i) ∧
          completedDownBatch W[k.val] i = some B ∧
          satisfies (samples B) w ∧ (∀ v, satisfies (samples B) v → v = w) ∧
          w ≠ CoordinatorLocalArmChoice.storedDownFlatWord M i ∧
          ReferenceDownReception.ordinaryLocalAcceptanceTest p rate W[k.val].input.time logged
            (ReferenceDownReception.ordinaryParse p rate (some w))) := by
  intro s R W k i logged cut hi hd
  rw [retained_wrongUniqueAccepted_iff W[k.val] i logged cut hi hd]
  constructor
  · rintro ⟨B, w, hB, hsol, huniq, hne, ha⟩
    obtain ⟨l, c, hl, hd', hcomp, _, _⟩ := (completedDownBatch_eq_some_iff W[k.val] i B).mp hB
    cases hi.symm.trans hl
    cases hd.symm.trans hd'
    obtain ⟨sel, birth, _, hbirth, htime, hborn, hsigma, _, hexpected, _⟩ :=
      actual_first_live_current_word rate source rewards C_star C_h count hc hspan k i logged cut hi hd hcomp
    refine ⟨sel.view.payload, birth, B, w, hsigma, hbirth, htime, hborn, hexpected,
      hB, hsol, huniq, ?_, ha⟩
    intro he
    apply hne
    rw [he, hexpected]
    rfl
  · rintro ⟨M, birth, B, w, _, _, _, _, hexpected, hB, hsol, huniq, hne, ha⟩
    refine ⟨B, w, hB, hsol, huniq, ?_, ha⟩
    rw [hexpected]
    exact fun he => hne (Option.some.inj he)

end ActualFirstLive

section SourceFiber

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s count : ℕ) (hspan : s + count ≤ p.T) (i : Fin (p.m - 1))

/-- Read the actual generated run, retaining all physical rounds and failures. -/
def sourceDownReadouts
    (x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s) :=
  (ReferenceActiveHorizonMeasurability.runOfInput s count hspan
    (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
      (rate := rate) rewards C_star C_h s x)).records.map (fun r => downReadout r i)

/-- Source-fibre reconstruction through the existing finite countable run code. -/
theorem sourceDownReadouts_eq_observation
    (x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s) :
    sourceDownReadouts rate rewards C_star C_h s count hspan i x =
      (List.ofFn (runDownObservation s count hspan i
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s x)).2).map observationReadout := by
  rw [(runDownObservation_eq_actual s count hspan i _).2, List.map_map]
  apply List.map_congr_left
  intro r _
  exact (observationReadout_actual r i).symm

/-- Arbitrary finite tests of completion, raw, ordinary acceptance and every
failure tag are Borel on a fixed launch fibre of the original source. -/
theorem measurableSet_sourceDownReadouts_test
    (P : List (Option (Batch p) × DownDiagnosticCode p rate) → Prop) :
    MeasurableSet {x | P (sourceDownReadouts rate rewards C_star C_h s count hspan i x)} := by
  have hm := (measurable_of_countable (fun code : RunDownObservationCode p rate count =>
    decide (P ((List.ofFn code.2).map observationReadout)))).comp
      ((measurable_runDownObservation s count hspan i).comp
        (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
          (rate := rate) rewards C_star C_h s))
  have hs := (measurableSet_singleton true).preimage hm
  convert hs using 1
  ext x
  simp only [Function.comp_apply, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq, sourceDownReadouts_eq_observation]

/-- The literal first-live list, clipped only by the admitted window producer. -/
def firstLiveDownReadouts
    (x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s) :=
  (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h s count hspan x).map
    (fun r => downReadout r i)

theorem firstLiveDownReadouts_eq_take
    (x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s) :
    firstLiveDownReadouts rate rewards C_star C_h s count hspan i x =
      (sourceDownReadouts rate rewards C_star C_h s count hspan i x).take
        (ReferenceFirstLiveOverflowReadout.firstLiveLength rate rewards C_star C_h s count hspan x) := by
  unfold firstLiveDownReadouts sourceDownReadouts
  rw [← ReferenceFirstLiveOverflowReadout.actualFirstLiveRun_eq_generated
    rate rewards C_star C_h s count hspan x, ← List.map_take]
  exact congrArg (List.map (fun r => downReadout r i))
    (List.prefix_iff_eq_take.mp (List.takeWhile_prefix _))

/-- Variable first-live clipping is obtained from O's admitted length API,
combined with the original countable run observation. No clipping assumption. -/
theorem measurableSet_firstLiveDownReadouts_test
    (P : List (Option (Batch p) × DownDiagnosticCode p rate) → Prop) :
    MeasurableSet {x | P (firstLiveDownReadouts rate rewards C_star C_h s count hspan i x)} := by
  have hcode := (measurable_runDownObservation s count hspan i).comp
    (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
      (rate := rate) rewards C_star C_h s)
  have hlen := ReferenceFirstLiveOverflowReadout.measurable_firstLiveLength
    rate rewards C_star C_h s count hspan
  have hm := (measurable_of_countable (fun code : ℕ × RunDownObservationCode p rate count =>
    decide (P (((List.ofFn code.2.2).map observationReadout).take code.1)))).comp
      (hlen.prodMk hcode)
  have hs := (measurableSet_singleton true).preimage hm
  convert hs using 1
  ext x
  simp only [Function.comp_apply, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq, firstLiveDownReadouts_eq_take, sourceDownReadouts_eq_observation]

end SourceFiber

section WholeSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- O's literal whole-source first-live window, with honest empty no-launch
and terminal cases. No competing stopping or overflow implementation. -/
def wholeFirstLiveDownReadouts (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :=
  (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h source).map
    (fun r => downReadout r i)

/-- Total original-source Borel tests, using the admitted launch fibres and
first-live clipping. This retains ALL original private arrays and J. -/
theorem measurableSet_wholeFirstLiveDownReadouts_test (i : Fin (p.m - 1))
    (P : List (Option (Batch p) × DownDiagnosticCode p rate) → Prop) :
    MeasurableSet {source | P (wholeFirstLiveDownReadouts rate rewards C_star C_h source i)} := by
  let E : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {source | P (wholeFirstLiveDownReadouts rate rewards C_star C_h source i)}
  let cover (tag : Option (Fin (p.T + 1))) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    match tag with
    | none => {source | (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none}
    | some s => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val
  have hcover (tag) : MeasurableSet (cover tag) := by
    cases tag with
    | none => exact ReferenceCorrectedLaunchMeasurability.measurableSet_generated_no_crossing rate rewards C_star C_h
    | some s => exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet rewards C_star C_h s.val
  have hcovered (source) : ∃ tag, source ∈ cover tag := by
    cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing with
    | none => exact ⟨none, hc⟩
    | some crossing =>
        exact ⟨some ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
          Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h)⟩,
          by simp only [cover, ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
            Set.mem_ofPred_eq, hc, Option.isSome_some, true_and]⟩
  have hrestricted (tag) : MeasurableSet {x : cover tag | x.val ∈ E} := by
    cases tag with
    | none =>
        have hempty (x : cover none) : wholeFirstLiveDownReadouts rate rewards C_star C_h x.val i = [] := by
          rw [wholeFirstLiveDownReadouts, (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
            rate rewards C_star C_h x.val x.property).1]
          rfl
        by_cases hP : P []
        · have hs : {x : cover none | x.val ∈ E} = Set.univ := by
            ext x; simp only [E, Set.mem_ofPred_eq, hempty x, hP, Set.mem_univ]
          rw [hs]; exact MeasurableSet.univ
        · have hs : {x : cover none | x.val ∈ E} = ∅ := by
            ext x; simp only [E, Set.mem_ofPred_eq, hempty x, hP, Set.mem_empty_iff_false]
          rw [hs]; exact MeasurableSet.empty
    | some s =>
        have hm := measurableSet_firstLiveDownReadouts_test rate rewards C_star C_h s.val
          (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) i P
        convert hm using 1
        ext x
        change P (wholeFirstLiveDownReadouts rate rewards C_star C_h x.val i) ↔ _
        unfold wholeFirstLiveDownReadouts firstLiveDownReadouts
        rw [(ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber rate rewards C_star C_h s x).1]
        rfl
  have heq : E = ⋃ tag, (Subtype.val : cover tag → _) '' {x | x.val ∈ E} := by
    ext source
    constructor
    · intro hx
      obtain ⟨tag, ht⟩ := hcovered source
      exact Set.mem_iUnion.mpr ⟨tag, ⟨source, ht⟩, hx, rfl⟩
    · intro hx
      obtain ⟨tag, x, hx, hxs⟩ := Set.mem_iUnion.mp hx
      exact hxs ▸ hx
  rw [show {source | P (wholeFirstLiveDownReadouts rate rewards C_star C_h source i)} = E from rfl, heq]
  exact MeasurableSet.iUnion fun tag => MeasurableSet.subtype_image (hcover tag) (hrestricted tag)

end WholeSource

end Bandits.Support.ReferenceFirstLiveDownCompletionReadout
