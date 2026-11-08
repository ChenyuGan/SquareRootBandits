/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveHorizonMeasurability
public import Bandits.Support.ReferenceActiveStoppedPrefixCoupling

/-!
# Borel saved-wrong-unique diagnostics on the existing active reference run

Sources: `sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:91-155`, and
`sources/zip4/manuscript/06_interruptions.tex:235-296,355-426`.

This internal producer reads the actual UP and DOWN diagnostic fields retained
by `ReferenceActiveHorizonMeasurability` and follows their existing decoders.
It measures saved wrong unique acceptance on chronological prefixes of the
existing physical `H.run`, and extracts the first such zero-based position.
The resulting stopped comparison consumes the existing conditional coupling
API. It does not define source `E_false`, its overflow window or probability,
and proves no manuscript or regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceActiveStoppedPrefixCoupling
open Bandits.Support.ReferenceCollectionServiceTailMeasurability
open Bandits.Support.ReferenceFollowerTailComposition
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ReferenceDownReceptionMeasurability

namespace Bandits.Support.ReferenceSavedWrongUniqueMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

-- Match H's existing countable clock-code factor when exposing intermediate
-- product projections of its full record space.
local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

private abbrev Code := ReferenceActiveHorizonMeasurability.RoundRecordCode
  (p := p) (rate := rate)

private abbrev FollowerCode := ReferenceFollowerTailComposition.FollowerObservable p rate

private abbrev DownCode := ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate

private abbrev UpCode := ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate

private abbrev CollectionCode :=
  ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate

/-- The DOWN diagnostic represented by one actual countable cut code.
`ordinaryAcceptance` is the exact Boolean encoding of the local acceptance
test, and all three conjuncts are the existing `wrongUniqueAccepted` fields. -/
def savedWrongCutCode
    (code : ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate) : Bool :=
  decide (code.rawComparison = some false ∧ code.raw ≠ none ∧
    code.ordinaryAcceptance = true)

/-- The UP diagnostic is read from the decoded actual collection observation;
an absent decoded UP diagnostic, including a failure branch, contributes
`false`. -/
def savedWrongUpCode
    (code : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate) : Bool :=
  match ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation code with
  | observation => observation.up.elim false fun diagnostic => diagnostic.wrongUniqueAccepted

/-- Decode the follower's DOWN cut with the original accompanying input tag.
In particular, `reconstructDown` returns `none` on the `inl` branch, even if
the product code happens to contain a cut. -/
def savedWrongFollowerCode
    (code : ReferenceFollowerTailComposition.FollowerObservable p rate) : Bool :=
  match ReferenceFollowerTailComposition.reconstructDown code.2.2.1 code.2.2.2 with
  | none => false
  | some _ =>
      match code.2.2.2 with
      | none => false
      | some cut => savedWrongCutCode cut

def roundRecordCollectionCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  code.2.2.1.2.2.2.2

def roundRecordFollowerCodes
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Fin (p.m - 1) → ReferenceFollowerTailComposition.FollowerObservable p rate := code.2.2.2.1

/-- Literal Boolean projection of an actual saved wrong unique acceptance in
the retained coordinator UP or actually-present follower DOWN diagnostics. -/
def savedWrongCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) : Bool :=
  savedWrongUpCode (roundRecordCollectionCode code) ||
    decide (∃ i : Fin (p.m - 1),
      savedWrongFollowerCode (roundRecordFollowerCodes code i) = true)

private def savedWrongCutCodeOption :
    Option (DownCode (p := p) (rate := rate)) → Bool
  | none => false
  | some code => savedWrongCutCode code

private def guardedSavedWrongDownCode
    (input : ReferenceFollowerTailComposition.DownInputObservable p rate ×
      Option (DownCode (p := p) (rate := rate))) : Bool :=
  match input.1 with
  | .inl _ => false
  | .inr _ => savedWrongCutCodeOption input.2

private theorem savedWrongCutCode_reconstructs
    (code : DownCode (p := p) (rate := rate))
    (buffer : List (SparseCalendarReplay.SparseCalendarRecord p.K)) :
    savedWrongCutCode code = true ↔
      ReferenceDownReception.wrongUniqueAccepted
        (ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode code buffer) := by
  simp [savedWrongCutCode, ReferenceDownReception.wrongUniqueAccepted,
    ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode,
    decide_eq_true_eq]

private theorem savedWrongFollowerCode_guarded
    (code : FollowerCode (p := p) (rate := rate)) :
    savedWrongFollowerCode code = guardedSavedWrongDownCode (code.2.2.1, code.2.2.2) := by
  cases hinput : code.2.2.1 with
  | inl absent =>
      simp [savedWrongFollowerCode, guardedSavedWrongDownCode,
        ReferenceFollowerTailComposition.reconstructDown, hinput]
  | inr carry =>
      cases hcut : code.2.2.2 with
      | none =>
          simp [savedWrongFollowerCode, guardedSavedWrongDownCode,
            savedWrongCutCodeOption,
            ReferenceFollowerTailComposition.reconstructDown, hinput, hcut]
      | some cut =>
          simp [savedWrongFollowerCode, guardedSavedWrongDownCode,
            savedWrongCutCodeOption,
            ReferenceFollowerTailComposition.reconstructDown, hinput, hcut]

private theorem measurable_savedWrongCutCode :
    Measurable (savedWrongCutCode (p := p) (rate := rate)) :=
  Measurable.of_discrete

private theorem measurable_savedWrongCutCodeOption :
    Measurable (savedWrongCutCodeOption (p := p) (rate := rate)) := by
  let e := Equiv.optionEquivSumPUnit (DownCode (p := p) (rate := rate))
  have he : Measurable e := comap_measurable _
  have hsum : Measurable (Sum.elim
      (savedWrongCutCode (p := p) (rate := rate)) (fun _ : PUnit => false)) :=
    measurable_savedWrongCutCode.sumElim measurable_const
  convert hsum.comp he using 1
  funext code
  cases code <;> rfl

private theorem measurable_guardedSavedWrongDownCode :
    Measurable (guardedSavedWrongDownCode (p := p) (rate := rate)) := by
  let distribute := MeasurableEquiv.sumProdDistrib Unit
    (FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
    (Option (DownCode (p := p) (rate := rate)))
  have hleft : Measurable (fun _ : Unit × Option (DownCode (p := p) (rate := rate)) => false) :=
    measurable_const
  have hright : Measurable (fun input :
      FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
      Option (DownCode (p := p) (rate := rate)) =>
      savedWrongCutCodeOption input.2) :=
    measurable_savedWrongCutCodeOption.comp measurable_snd
  have hsum : Measurable (fun input :
      ReferenceFollowerTailComposition.DownInputObservable p rate ×
        Option (DownCode (p := p) (rate := rate)) =>
      Sum.elim (fun _ : Unit × Option (DownCode (p := p) (rate := rate)) => false)
        (fun x : FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
          Option (DownCode (p := p) (rate := rate)) =>
          savedWrongCutCodeOption x.2) (distribute input)) :=
    (hleft.sumElim hright).comp distribute.measurable
  convert hsum using 1
  funext input
  cases input with
  | mk tag cut => cases tag <;> rfl

private theorem measurable_savedWrongFollowerCode :
    Measurable (savedWrongFollowerCode (p := p) (rate := rate)) := by
  have hdown : Measurable (fun code : FollowerCode (p := p) (rate := rate) =>
      code.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hcut : Measurable (fun code : FollowerCode (p := p) (rate := rate) =>
      code.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hdata : Measurable (fun code : FollowerCode (p := p) (rate := rate) =>
      (code.2.2.1, code.2.2.2)) := hdown.prodMk hcut
  have heq : savedWrongFollowerCode (p := p) (rate := rate) =
      fun code : FollowerCode (p := p) (rate := rate) =>
        guardedSavedWrongDownCode (code.2.2.1, code.2.2.2) := by
    funext code
    exact savedWrongFollowerCode_guarded code
  rw [heq]
  exact measurable_guardedSavedWrongDownCode.comp hdata

private theorem measurable_roundRecordCollectionCode :
    Measurable (roundRecordCollectionCode (p := p) (rate := rate)) := by
  have hphysical : Measurable (fun code : Code (p := p) (rate := rate) => code.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hphysicalTail1 : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.PhysicalCode (p := p) (rate := rate) => code.2) :=
    measurable_snd
  have hphysicalTail2 : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.PhysicalCode (p := p) (rate := rate) => code.2.2) :=
    measurable_snd.comp hphysicalTail1
  have hphysicalTail3 : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.PhysicalCode (p := p) (rate := rate) => code.2.2.2) :=
    measurable_snd.comp hphysicalTail2
  have htail : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.PhysicalCode (p := p) (rate := rate) =>
      code.2.2.2.2) := measurable_snd.comp hphysicalTail3
  exact htail.comp hphysical

private theorem measurable_savedWrongUpCode :
    Measurable (savedWrongUpCode (p := p) (rate := rate)) := by
  have hdiagnostic : Measurable (fun code : CollectionCode (p := p) (rate := rate) =>
      code.2.2.2.2) := by
    have h1 : Measurable (fun code : CollectionCode (p := p) (rate := rate) => code.2) :=
      measurable_snd
    have h2 : Measurable (fun code : CollectionCode (p := p) (rate := rate) => code.2.2) :=
      measurable_snd.comp h1
    have h3 : Measurable (fun code : CollectionCode (p := p) (rate := rate) => code.2.2.2) :=
      measurable_snd.comp h2
    exact measurable_snd.comp h3
  have hflag : Measurable (fun diagnostic : Option (UpCode (p := p) (rate := rate)) =>
      diagnostic.elim false fun value => value.wrongUniqueAccepted) := Measurable.of_discrete
  have heq : savedWrongUpCode = fun code : CollectionCode (p := p) (rate := rate) =>
      (code.2.2.2.2).elim false fun value => value.wrongUniqueAccepted := by
    funext code
    cases h : code.2.2.2.2 with
    | none =>
        simp [savedWrongUpCode,
          ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation, h]
    | some diagnostic =>
        simp [savedWrongUpCode,
          ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation,
          ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic, h]
  rw [heq]
  exact hflag.comp hdiagnostic

private theorem measurable_productFollowerProjection {α β γ δ ε : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε] :
    Measurable (fun code : α × (β × (γ × (δ × ε))) => code.2.2.2.1) :=
  measurable_snd.snd.snd.fst

private theorem measurable_roundRecordFollowerCodes :
    Measurable (roundRecordFollowerCodes (p := p) (rate := rate)) :=
  measurable_productFollowerProjection

private theorem measurable_savedWrongFollowersCode :
    Measurable (fun followers : Fin (p.m - 1) → FollowerCode (p := p) (rate := rate) =>
      decide (∃ i : Fin (p.m - 1), savedWrongFollowerCode (followers i) = true)) := by
  classical
  have hbad (i : Fin (p.m - 1)) :
      Measurable (fun followers : Fin (p.m - 1) → FollowerCode (p := p) (rate := rate) =>
        savedWrongFollowerCode (followers i)) :=
    measurable_savedWrongFollowerCode.comp (measurable_pi_apply i)
  have hset : {followers : Fin (p.m - 1) → FollowerCode (p := p) (rate := rate) |
      ∃ i : Fin (p.m - 1), savedWrongFollowerCode (followers i) = true} =
      ⋃ i : Fin (p.m - 1), {followers | savedWrongFollowerCode (followers i) = true} := by
    ext followers
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  have hmeas : MeasurableSet {followers : Fin (p.m - 1) → FollowerCode (p := p) (rate := rate) |
      ∃ i : Fin (p.m - 1), savedWrongFollowerCode (followers i) = true} := by
    rw [hset]
    exact MeasurableSet.iUnion fun i => hbad i (measurableSet_singleton true)
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro bit
  cases bit
  · have hfalse : {followers : Fin (p.m - 1) → FollowerCode (p := p) (rate := rate) |
        decide (∃ i : Fin (p.m - 1), savedWrongFollowerCode (followers i) = true) = false} =
        {followers | ¬ ∃ i : Fin (p.m - 1),
          savedWrongFollowerCode (followers i) = true} := by
      ext followers
      simp only [Set.mem_ofPred_eq, decide_eq_false_iff_not]
    rw [hfalse]
    exact hmeas.compl
  · have htrue : {followers : Fin (p.m - 1) → FollowerCode (p := p) (rate := rate) |
        decide (∃ i : Fin (p.m - 1), savedWrongFollowerCode (followers i) = true) = true} =
        {followers | ∃ i : Fin (p.m - 1),
          savedWrongFollowerCode (followers i) = true} := by
      ext followers
      simp [decide_eq_true_eq]
    rw [htrue]
    exact hmeas

/-- Saved-wrong-unique acceptance is Borel on the unchanged full record code.
Only the countable UP/DOWN diagnostic fibres are projected; all continuous
buffer, row and scalar fibres retain their original measurable spaces. -/
theorem measurable_savedWrongCode : Measurable (savedWrongCode (p := p) (rate := rate)) := by
  have hup := (measurable_savedWrongUpCode (p := p) (rate := rate)).comp
    (measurable_roundRecordCollectionCode (p := p) (rate := rate))
  have hfollower := (measurable_savedWrongFollowersCode (p := p) (rate := rate)).comp
    (measurable_roundRecordFollowerCodes (p := p) (rate := rate))
  exact (measurable_of_finite (fun bits : Bool × Bool => bits.1 || bits.2)).comp
    (hup.prodMk hfollower)

private theorem savedWrongUpCode_true_iff
    (code : CollectionCode (p := p) (rate := rate)) :
    savedWrongUpCode code = true ↔
      ∃ diagnostic,
        (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation code).up =
          some diagnostic ∧ diagnostic.wrongUniqueAccepted = true := by
  cases hobs : ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation code with
  | mk configuration bank failure recording up =>
      cases up <;> simp [savedWrongUpCode, hobs]

private theorem savedWrongFollowerCode_true_iff
    (code : FollowerCode (p := p) (rate := rate)) :
    savedWrongFollowerCode code = true ↔
      ∃ cut,
        ReferenceFollowerTailComposition.reconstructDown code.2.2.1 code.2.2.2 = some cut ∧
          ReferenceDownReception.wrongUniqueAccepted cut := by
  cases hinput : code.2.2.1 with
  | inl absent =>
      simp [savedWrongFollowerCode, ReferenceFollowerTailComposition.reconstructDown, hinput]
  | inr carry =>
      cases hcode : code.2.2.2 with
      | none =>
          simp [savedWrongFollowerCode, ReferenceFollowerTailComposition.reconstructDown,
            hinput, hcode]
      | some cut =>
          simpa [savedWrongFollowerCode, ReferenceFollowerTailComposition.reconstructDown,
            hinput, hcode] using
            (savedWrongCutCode_reconstructs cut
              (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer carry))

private theorem savedWrongCode_true_iff (code : Code (p := p) (rate := rate)) :
    savedWrongCode code = true ↔
      (∃ diagnostic,
        (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
          (roundRecordCollectionCode code)).up = some diagnostic ∧
          diagnostic.wrongUniqueAccepted = true) ∨
      (∃ i cut,
        ReferenceFollowerTailComposition.reconstructDown
            ((roundRecordFollowerCodes code i).2.2.1)
            ((roundRecordFollowerCodes code i).2.2.2) = some cut ∧
          ReferenceDownReception.wrongUniqueAccepted cut) := by
  unfold savedWrongCode
  rw [Bool.or_eq_true, savedWrongUpCode_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro (hup | ⟨i, hbad⟩)
    · exact Or.inl hup
    · rcases (savedWrongFollowerCode_true_iff (roundRecordFollowerCodes code i)).1 hbad with
        ⟨cut, hcut, hwrong⟩
      exact Or.inr ⟨i, cut, hcut, hwrong⟩
  · rintro (hup | ⟨i, cut, hcut, hwrong⟩)
    · exact Or.inl hup
    · exact Or.inr ⟨i,
        (savedWrongFollowerCode_true_iff (roundRecordFollowerCodes code i)).2
          ⟨cut, hcut, hwrong⟩⟩

/-- The retained Boolean is exactly the literal saved diagnostic predicate on
every actual horizon record. The two reconstruction equations are those of
the admitted observation decoder; no step is run again. -/
theorem savedWrongCode_roundRecord_iff
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    savedWrongCode (ReferenceActiveHorizonMeasurability.roundRecordCode record) = true ↔
      ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record := by
  have hdecode :=
    ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record
  have hup :
      (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (roundRecordCollectionCode
          (ReferenceActiveHorizonMeasurability.roundRecordCode record))).up =
        record.output.coordinator.up := by
    have h := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.up hdecode.2.1
    simpa [roundRecordCollectionCode,
      ReferenceActiveHorizonMeasurability.roundRecordCode,
      ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics] using h
  have hdown (i : Fin (p.m - 1)) :
      ReferenceFollowerTailComposition.reconstructDown
          ((roundRecordFollowerCodes
            (ReferenceActiveHorizonMeasurability.roundRecordCode record)) i).2.2.1
          ((roundRecordFollowerCodes
            (ReferenceActiveHorizonMeasurability.roundRecordCode record)) i).2.2.2 =
        (record.output.followers i).down := by
    have h := congrArg ReferenceActivePhysicalStep.FollowerObservation.down
      (hdecode.2.2.1 i)
    simpa [roundRecordFollowerCodes,
      ReferenceActiveHorizonMeasurability.roundRecordCode,
      ReferenceFollowerTailComposition.reconstructFollowerObservable,
      ReferenceActivePhysicalHorizon.RoundRecord.followerDiagnostics] using h
  rw [savedWrongCode_true_iff]
  simp_rw [hup, hdown]
  rfl

def savedWrongCodeAtTag
    (tag : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool :=
  tag.elim (fun _ => false) savedWrongCode

private theorem measurable_savedWrongCodeAtTag :
    Measurable (savedWrongCodeAtTag (p := p) (rate := rate)) :=
  Measurable.sumElim measurable_const
    (measurable_savedWrongCode (p := p) (rate := rate))

def savedWrongCodeAt
    (codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)))
    (index : ℕ) : Bool :=
  savedWrongCodeAtTag (ReferenceActiveHorizonMeasurability.listObservationAt codes index)

private theorem measurable_listObservationAt (index : ℕ) :
    Measurable (fun codes : List (Code (p := p) (rate := rate)) =>
      ReferenceActiveHorizonMeasurability.listObservationAt codes index) := by
  have hcoordinates : Measurable
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (α := Code (p := p) (rate := rate))) :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
  have hstream := (measurable_pi_apply index).comp (measurable_snd.comp hcoordinates)
  have heq : (fun codes : List (Code (p := p) (rate := rate)) =>
      ReferenceActiveHorizonMeasurability.listObservationAt codes index) =
      fun codes =>
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates codes).2 index := rfl
  rw [heq]
  exact hstream

private theorem savedWrongCodeAt_eq_getElem
    (codes : List (Code (p := p) (rate := rate))) (index : ℕ)
    (hindex : index < codes.length) :
    savedWrongCodeAt codes index = savedWrongCode codes[index] := by
  simp [savedWrongCodeAt, savedWrongCodeAtTag,
    ReferenceActiveHorizonMeasurability.listObservationAt,
    List.getElem?_eq_getElem hindex]

/-- Existence in the literal first `count` records of the same chronological
code list. -/
def savedWrongPrefixCode (count : ℕ)
    (codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))) : Bool :=
  (codes.take count).any savedWrongCode

private theorem savedWrongPrefixCode_true_iff_mem
    (count : ℕ) (codes : List (Code (p := p) (rate := rate))) :
    savedWrongPrefixCode count codes = true ↔
      ∃ code ∈ codes.take count, savedWrongCode code = true := by
  change (codes.take count).any savedWrongCode = true ↔ _
  rw [List.any_eq_true]

private theorem savedWrongPrefixCode_true_iff_indexed
    (count : ℕ) (codes : List (Code (p := p) (rate := rate))) :
    savedWrongPrefixCode count codes = true ↔
      ∃ index, index < count ∧ savedWrongCodeAt codes index = true := by
  unfold savedWrongPrefixCode
  rw [List.any_eq_true]
  constructor
  · rintro ⟨code, hmem, hbad⟩
    rcases List.mem_take_iff_getElem.mp hmem with ⟨index, hindex, hcode⟩
    have hcount : index < count := lt_of_lt_of_le hindex (Nat.min_le_left _ _)
    have hlen : index < codes.length := lt_of_lt_of_le hindex (Nat.min_le_right _ _)
    refine ⟨index, hcount, ?_⟩
    rw [savedWrongCodeAt_eq_getElem codes index hlen, hcode]
    exact hbad
  · rintro ⟨index, hcount, hbad⟩
    cases htag : ReferenceActiveHorizonMeasurability.listObservationAt codes index with
    | inl missing => simp [savedWrongCodeAt, savedWrongCodeAtTag, htag] at hbad
    | inr code =>
        have hget : codes[index]? = some code := by
          cases hindexGet : codes[index]? with
          | none => simp [ReferenceActiveHorizonMeasurability.listObservationAt, hindexGet] at htag
          | some actual =>
              have hactual : actual = code := by
                simpa [ReferenceActiveHorizonMeasurability.listObservationAt, hindexGet] using htag
              subst code
              rfl
        rcases List.getElem?_eq_some_iff.mp hget with ⟨hlen, hcode⟩
        have hmem : code ∈ codes.take count :=
          List.mem_take_iff_getElem.mpr ⟨index,
            (Nat.lt_min).2 ⟨hcount, hlen⟩, hcode⟩
        exact ⟨code, hmem, by simpa [savedWrongCodeAt, savedWrongCodeAtTag, htag] using hbad⟩

private theorem savedWrongPrefixCode_false_iff_indexed
    (count : ℕ) (codes : List (Code (p := p) (rate := rate))) :
    savedWrongPrefixCode count codes = false ↔
      ∀ index, index < count → savedWrongCodeAt codes index = false := by
  cases h : savedWrongPrefixCode count codes with
  | false =>
      constructor
      · intro _ index hindex
        cases hbad : savedWrongCodeAt codes index <;> simp_all
        have hex : savedWrongPrefixCode count codes = true :=
          (savedWrongPrefixCode_true_iff_indexed count codes).2 ⟨index, hindex, hbad⟩
        rw [h] at hex
        contradiction
      · intro _
        rfl
  | true =>
      constructor
      · intro hfalse
        cases hfalse
      · intro hsafe
        have hnot : ¬ savedWrongPrefixCode count codes = true := by
          intro htrue
          rcases (savedWrongPrefixCode_true_iff_indexed count codes).1 htrue with
            ⟨index, hindex, hbad⟩
          rw [hsafe index hindex] at hbad
          contradiction
        exact False.elim (hnot h)

private theorem measurable_savedWrongPrefixCode :
    Measurable (fun input : ℕ × List (Code (p := p) (rate := rate)) =>
      savedWrongPrefixCode input.1 input.2) := by
  have hcoordinates : Measurable (fun input : ℕ × List (Code (p := p) (rate := rate)) =>
      ReferenceActiveHorizonMeasurability.listObservationCoordinates input.2) :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp measurable_snd
  have hindexTag (index : ℕ) : Measurable (fun input : ℕ × List (Code (p := p) (rate := rate)) =>
      ReferenceActiveHorizonMeasurability.listObservationAt input.2 index) := by
    have h := (measurable_pi_apply index).comp (measurable_snd.comp hcoordinates)
    have heq : (fun input : ℕ × List (Code (p := p) (rate := rate)) =>
        ReferenceActiveHorizonMeasurability.listObservationAt input.2 index) =
        fun input => (ReferenceActiveHorizonMeasurability.listObservationCoordinates input.2).2 index := rfl
    rw [heq]
    exact h
  have hbad (index : ℕ) : Measurable (fun input : ℕ × List (Code (p := p) (rate := rate)) =>
      savedWrongCodeAtTag
        (ReferenceActiveHorizonMeasurability.listObservationAt input.2 index)) :=
    measurable_savedWrongCodeAtTag.comp (hindexTag index)
  have hlt (index : ℕ) : Measurable (fun input : ℕ × List (Code (p := p) (rate := rate)) =>
      decide (index < input.1)) :=
    (Measurable.of_discrete (f := fun n : ℕ => decide (index < n))).comp measurable_fst
  have hset : {input : ℕ × List (Code (p := p) (rate := rate)) |
      ∃ index, decide (index < input.1) = true ∧
        savedWrongCodeAt input.2 index = true} =
      ⋃ index : ℕ, {input | decide (index < input.1) = true} ∩
        {input | savedWrongCodeAt input.2 index = true} := by
    ext input
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  have hmeas : MeasurableSet {input : ℕ × List (Code (p := p) (rate := rate)) |
      ∃ index, index < input.1 ∧
        savedWrongCodeAt input.2 index = true} := by
    have hmeasBool : MeasurableSet {input : ℕ × List (Code (p := p) (rate := rate)) |
        ∃ index, decide (index < input.1) = true ∧
          savedWrongCodeAt input.2 index = true} := by
      rw [hset]
      exact MeasurableSet.iUnion fun index =>
        (hlt index (measurableSet_singleton true)).inter
          (hbad index (measurableSet_singleton true))
    simpa only [decide_eq_true_eq] using hmeasBool
  have htrueSet : {input : ℕ × List (Code (p := p) (rate := rate)) |
      savedWrongPrefixCode input.1 input.2 = true} =
      {input | ∃ index, index < input.1 ∧
        savedWrongCodeAt input.2 index = true} := by
    ext input
    exact savedWrongPrefixCode_true_iff_indexed input.1 input.2
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro bit
  cases bit
  · have hfalseSet : {input : ℕ × List (Code (p := p) (rate := rate)) |
        savedWrongPrefixCode input.1 input.2 = false} =
        {input | savedWrongPrefixCode input.1 input.2 = true}ᶜ := by
      ext input
      cases savedWrongPrefixCode input.1 input.2 <;> simp
    rw [hfalseSet, htrueSet]
    exact hmeas.compl
  · rw [htrueSet]
    exact hmeas

/-- Prefix existence on the fixed-start, fixed-count original active run. -/
def runSavedWrongPrefixCode (start count : ℕ) (hspan : start + count ≤ p.T)
    (prefixCount : ℕ)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start) : Bool :=
  savedWrongPrefixCode prefixCount
    (ReferenceActiveHorizonMeasurability.runObservation start count hspan input).2

theorem measurable_runSavedWrongPrefixCode (start count : ℕ)
    (hspan : start + count ≤ p.T) (prefixCount : ℕ) :
    Measurable (runSavedWrongPrefixCode (p := p) (rate := rate)
      start count hspan prefixCount) := by
  exact measurable_savedWrongPrefixCode.comp
    (measurable_const.prodMk
      (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_runObservation start count hspan)))

/-- Prefix existence on the existing varying-calendar run observation. -/
def calendarSavedWrongPrefixCode
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (prefixCount : ℕ) : Bool :=
  savedWrongPrefixCode prefixCount
    (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2

theorem measurable_calendarSavedWrongPrefixCode (prefixCount : ℕ) :
    Measurable (calendarSavedWrongPrefixCode (p := p) (rate := rate) · prefixCount) := by
  exact measurable_savedWrongPrefixCode.comp
    (measurable_const.prodMk
      (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_calendarRunObservation
          (p := p) (rate := rate))))

/-- The count itself varies with the calendar input; this is joint Borel in
the prefixCount index and the original calendar subtype. -/
def calendarSavedWrongPrefixCodeJoint
    (input : ℕ × ReferenceActiveHorizonMeasurability.CalendarRunInput
      (p := p) (rate := rate)) : Bool :=
  savedWrongPrefixCode input.1
    (ReferenceActiveHorizonMeasurability.calendarRunObservation input.2).2

theorem measurable_calendarSavedWrongPrefixCodeJoint :
    Measurable (calendarSavedWrongPrefixCodeJoint (p := p) (rate := rate)) := by
  exact measurable_savedWrongPrefixCode.comp
    (measurable_fst.prodMk
      ((measurable_snd.comp
          (ReferenceActiveHorizonMeasurability.measurable_calendarRunObservation
            (p := p) (rate := rate))).comp measurable_snd))

def calendarFixedInput
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :
    ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) input.val.1 :=
  ⟨input.val.2.2, input.property.2⟩

private theorem calendarRunObservation_recordCount
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :
    (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2.length =
      input.val.2.1 := by
  rw [ReferenceActiveHorizonMeasurability.calendarRunObservation_eq_actual]
  exact ReferenceActiveHorizonMeasurability.runObservation_recordCount
    input.val.1 input.val.2.1 input.property.1 (calendarFixedInput input)

def calendarReferenceRun
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :=
  ReferenceActiveHorizonMeasurability.runOfInput input.val.1 input.val.2.1
    input.property.1 (calendarFixedInput input)

def calendarReferenceRecordAt
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (index : ℕ) (hindex : index < input.val.2.1) :=
  ReferenceActiveStoppedPrefixCoupling.referenceRecordAt input.val.2.2.1
    input.val.2.2.2.1 input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1
    index (by omega) input.property.2

/-- Existence in a fixed run code prefixCount is exactly existence of the
corresponding saved diagnostic on an actual record of `H.run.records.take k`.
-/
theorem runSavedWrongPrefixCode_true_iff (start count : ℕ)
    (hspan : start + count ≤ p.T) (prefixCount : ℕ)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start) :
    runSavedWrongPrefixCode start count hspan prefixCount input = true ↔
      ∃ record ∈
        (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records.take prefixCount,
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record := by
  unfold runSavedWrongPrefixCode
  rw [savedWrongPrefixCode_true_iff_mem]
  rw [ReferenceActiveHorizonMeasurability.runObservation_records, ← List.map_take]
  constructor
  · rintro ⟨code, hcode, hbad⟩
    rcases List.mem_map.mp hcode with ⟨record, hrecord, rfl⟩
    exact ⟨record, hrecord,
      (savedWrongCode_roundRecord_iff record).mp hbad⟩
  · rintro ⟨record, hrecord, hbad⟩
    exact ⟨ReferenceActiveHorizonMeasurability.roundRecordCode record,
      List.mem_map.mpr ⟨record, hrecord, rfl⟩,
      (savedWrongCode_roundRecord_iff record).mpr hbad⟩

theorem runSavedWrongPrefixCode_false_iff (start count : ℕ)
    (hspan : start + count ≤ p.T) (prefixCount : ℕ)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start) :
    runSavedWrongPrefixCode start count hspan prefixCount input = false ↔
      ∀ record ∈
        (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records.take prefixCount,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
  have hbool : runSavedWrongPrefixCode start count hspan prefixCount input = false ↔
      ¬ runSavedWrongPrefixCode start count hspan prefixCount input = true := by
    exact Bool.eq_false_iff
  rw [hbool, runSavedWrongPrefixCode_true_iff]
  constructor
  · intro h record hrecord
    exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).2
      (fun hbad => h ⟨record, hrecord, hbad⟩)
  · intro h ⟨record, hrecord, hbad⟩
    exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).1
      (h record hrecord) hbad

theorem calendarSavedWrongPrefixCode_true_iff
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (prefixCount : ℕ) :
    calendarSavedWrongPrefixCode input prefixCount = true ↔
      ∃ record ∈ (calendarReferenceRun input).records.take prefixCount,
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record := by
  unfold calendarSavedWrongPrefixCode
  rw [ReferenceActiveHorizonMeasurability.calendarRunObservation_eq_actual]
  exact runSavedWrongPrefixCode_true_iff input.val.1 input.val.2.1
    input.property.1 prefixCount (calendarFixedInput input)

theorem calendarSavedWrongPrefixCode_false_iff
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (prefixCount : ℕ) :
    calendarSavedWrongPrefixCode input prefixCount = false ↔
      ∀ record ∈ (calendarReferenceRun input).records.take prefixCount,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
  unfold calendarSavedWrongPrefixCode
  rw [ReferenceActiveHorizonMeasurability.calendarRunObservation_eq_actual]
  exact runSavedWrongPrefixCode_false_iff input.val.1 input.val.2.1
    input.property.1 prefixCount (calendarFixedInput input)

/-- Existence in the complete literal record list of the varying `H.run`. -/
def calendarSavedWrongCode
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) : Bool :=
  calendarSavedWrongPrefixCode input input.val.2.1

theorem measurable_calendarSavedWrongCode :
    Measurable (calendarSavedWrongCode (p := p) (rate := rate)) := by
  have hcount : Measurable (fun input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) =>
      input.val.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
  have hcodes := measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_calendarRunObservation
      (p := p) (rate := rate))
  exact measurable_savedWrongPrefixCode.comp (hcount.prodMk hcodes)

theorem calendarSavedWrongCode_true_iff
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :
    calendarSavedWrongCode input = true ↔
      ∃ record ∈ (calendarReferenceRun input).records,
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record := by
  have hlen : (calendarReferenceRun input).records.length = input.val.2.1 := by
    dsimp [calendarReferenceRun,
      ReferenceActiveHorizonMeasurability.runOfInput, calendarFixedInput]
    exact ReferenceActivePhysicalHorizon.run_record_count input.val.2.2.1
      input.val.2.2.2.1 input.val.2.2.2.2.1 input.val.2.2.2.2.2
      input.val.1 input.val.2.1 input.property.1 input.property.2
  rw [calendarSavedWrongCode, calendarSavedWrongPrefixCode_true_iff]
  rw [List.take_of_length_le (Nat.le_of_eq hlen)]

theorem calendarSavedWrongCode_false_iff
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :
    calendarSavedWrongCode input = false ↔
      ∀ record ∈ (calendarReferenceRun input).records,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
  have hbool : calendarSavedWrongCode input = false ↔
      ¬ calendarSavedWrongCode input = true := by
    exact Bool.eq_false_iff
  rw [hbool, calendarSavedWrongCode_true_iff]
  constructor
  · intro h record hrecord
    exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).2
      (fun hbad => h ⟨record, hrecord, hbad⟩)
  · intro h ⟨record, hrecord, hbad⟩
    exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).1
      (h record hrecord) hbad

/-- The zero-based first true position in the literal chronological code list
of the same `H.calendarRunObservation`. -/
def firstSavedWrongOffset
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :
    Option ℕ :=
  ((ReferenceActiveHorizonMeasurability.calendarRunObservation input).2).findIdx? savedWrongCode

/-- The named reference record occupies exactly this chronological list slot. -/
theorem calendarReferenceRecordAt_getElem?
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (index : ℕ) (hindex : index < input.val.2.1) :
    (calendarReferenceRun input).records[index]? = some (calendarReferenceRecordAt input index hindex) := by
  let initial := input.val.2.2.1
  let rows := input.val.2.2.2.1
  let selected := input.val.2.2.2.2.1
  let rewards := input.val.2.2.2.2.2
  let start := input.val.1
  let count := input.val.2.1
  change (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      input.property.1 input.property.2).records[index]? = _
  calc
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        input.property.1 input.property.2).records[index]? =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        input.property.1 input.property.2).records.take (index + 1))[index]? := by
          rw [List.getElem?_take_of_lt (by omega)]
    _ = (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
        (by omega) input.property.2).records[index]? := by
          rw [ReferenceActiveStoppedPrefixCoupling.reference_run_prefix_records
            initial rows selected rewards start count input.property.1 input.property.2
            (index + 1) (by omega)]
    _ = some (ReferenceActiveStoppedPrefixCoupling.referenceRecordAt
        initial rows selected rewards start index (by omega) input.property.2) := by
          rw [(ReferenceActiveStoppedPrefixCoupling.reference_successor_equations
            initial rows selected rewards start index (by omega) input.property.2).2]
          rw [List.getElem?_append_right (by
            rw [ReferenceActivePhysicalHorizon.run_record_count])]
          simp [ReferenceActivePhysicalHorizon.run_record_count]

private theorem calendarCodeAt_referenceRecordAt
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (index : ℕ) (hindex : index < input.val.2.1) :
    (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2[index]? =
      some (ReferenceActiveHorizonMeasurability.roundRecordCode
        (calendarReferenceRecordAt input index hindex)) := by
  rw [ReferenceActiveHorizonMeasurability.calendarRunObservation_eq_actual,
    ReferenceActiveHorizonMeasurability.runObservation_records,
    List.getElem?_map]
  exact congrArg (Option.map ReferenceActiveHorizonMeasurability.roundRecordCode)
    (calendarReferenceRecordAt_getElem? input index hindex)

private theorem firstSavedWrongOffset_some_iff_code_positions
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (index : ℕ) :
    firstSavedWrongOffset input = some index ↔
      ∃ hindex : index < (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2.length,
        savedWrongCode
            ((ReferenceActiveHorizonMeasurability.calendarRunObservation input).2[index]'hindex) = true ∧
        ∀ earlier (hearlier : earlier < index),
          savedWrongCode
              ((ReferenceActiveHorizonMeasurability.calendarRunObservation input).2[earlier]'
                (Nat.lt_trans hearlier hindex)) = false := by
  unfold firstSavedWrongOffset
  rw [List.findIdx?_eq_some_iff_getElem]
  simp only [Bool.not_eq_true]

theorem firstSavedWrongOffset_some_iff_indexed
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (index : ℕ) :
    firstSavedWrongOffset input = some index ↔
      index < input.val.2.1 ∧
        savedWrongCodeAt (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2
          index = true ∧
        ∀ earlier, earlier < index →
          savedWrongCodeAt (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2
            earlier = false := by
  have hlen := calendarRunObservation_recordCount input
  rw [firstSavedWrongOffset_some_iff_code_positions]
  constructor
  · rintro ⟨hindex, hbad, hsafe⟩
    have hcount : index < input.val.2.1 := by rw [← hlen]; exact hindex
    refine ⟨hcount, ?_, ?_⟩
    · rw [savedWrongCodeAt_eq_getElem _ index hindex]
      exact hbad
    · intro earlier hearlier
      rw [savedWrongCodeAt_eq_getElem _ earlier (Nat.lt_trans hearlier hindex)]
      exact hsafe earlier hearlier
  · rintro ⟨hindex, hbad, hsafe⟩
    have hindexCode : index <
        (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2.length := by
      rw [hlen]
      exact hindex
    refine ⟨hindexCode, ?_, ?_⟩
    · rw [savedWrongCodeAt_eq_getElem _ index hindexCode] at hbad
      exact hbad
    · intro earlier hearlier
      have hsafeAt := hsafe earlier hearlier
      rw [savedWrongCodeAt_eq_getElem _ earlier (Nat.lt_trans hearlier hindexCode)] at hsafeAt
      exact hsafeAt

private theorem measurable_calendarSavedWrongCodeAt (index : ℕ) :
    Measurable (fun input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) =>
      savedWrongCodeAt (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 index) := by
  have hcodes := measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_calendarRunObservation
      (p := p) (rate := rate))
  exact measurable_savedWrongCodeAtTag.comp
    ((measurable_listObservationAt index).comp hcodes)

/-- Each `some k` fibre records a bad code at `k`, all earlier safe codes, and
the actual finite run bound. The countable intersection keeps its original
continuous-input measurable structure. -/
private theorem measurable_firstSavedWrongOffset_some (index : ℕ) :
    MeasurableSet {input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
      firstSavedWrongOffset input = some index} := by
  have hcount : Measurable (fun input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) =>
      input.val.2.1) := measurable_fst.comp
        (measurable_snd.comp measurable_subtype_coe)
  have hlt : Measurable (fun input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) =>
      decide (index < input.val.2.1)) :=
    (Measurable.of_discrete (f := fun n : ℕ => decide (index < n))).comp hcount
  have hAt (j : ℕ) : Measurable (fun input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) =>
      savedWrongCodeAt
        (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 j) :=
    measurable_calendarSavedWrongCodeAt j
  have hbound : MeasurableSet {input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
      index < input.val.2.1} := by
    have hset : {input :
        ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
        index < input.val.2.1} =
        (fun input => decide (index < input.val.2.1)) ⁻¹' ({true} : Set Bool) := by
      ext input
      simp [decide_eq_true_eq]
    rw [hset]
    exact hlt (measurableSet_singleton true)
  have hbad : MeasurableSet {input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
      savedWrongCodeAt
        (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 index = true} :=
    hAt index (measurableSet_singleton true)
  have hsafe : MeasurableSet {input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
      ∀ earlier, earlier < index →
        savedWrongCodeAt
          (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 earlier = false} := by
    have hset : {input :
        ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
        ∀ earlier, earlier < index →
          savedWrongCodeAt
            (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 earlier = false} =
        ⋂ earlier : ℕ,
          {input | savedWrongCodeAt
            (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 earlier = false} ∪
          {input | index ≤ earlier} := by
      ext input
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro hs earlier
        by_cases hj : earlier < index
        · exact Or.inl (hs earlier hj)
        · exact Or.inr (Nat.le_of_not_gt hj)
      · intro hs earlier hj
        exact (hs earlier).resolve_right (not_le_of_gt hj)
    rw [hset]
    apply MeasurableSet.iInter
    intro earlier
    apply MeasurableSet.union
    · exact hAt earlier (measurableSet_singleton false)
    · exact MeasurableSet.const (index ≤ earlier)
  have hset : {input :
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
      firstSavedWrongOffset input = some index} =
      {input | index < input.val.2.1 ∧
        savedWrongCodeAt
          (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 index = true ∧
        ∀ earlier, earlier < index →
          savedWrongCodeAt
            (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 earlier = false} := by
    ext input
    exact firstSavedWrongOffset_some_iff_indexed input index
  rw [hset]
  exact hbound.inter (hbad.inter hsafe)

/-- The first-position result is Borel on the original calendar input space;
the absent fibre is the complement of all countably many `some k` fibres. -/
theorem measurable_firstSavedWrongOffset :
    Measurable (firstSavedWrongOffset (p := p) (rate := rate)) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro value
  cases value with
  | some index => exact measurable_firstSavedWrongOffset_some index
  | none =>
      have hset : {input :
          ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) |
          firstSavedWrongOffset input = none} =
          ⋂ index : ℕ, {input | firstSavedWrongOffset input ≠ some index} := by
        ext input
        cases h : firstSavedWrongOffset input <;> simp [h]
      rw [hset]
      apply MeasurableSet.iInter
      intro index
      exact (measurable_firstSavedWrongOffset_some index).compl

/-- A present offset names an actual saved bad record in the computed run,
and every actual record in the strict earlier prefixCount is safe. The detecting
record is included in the prefixCount ending at `index + 1`. -/
theorem firstSavedWrongOffset_some_spec
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    {index : ℕ} (hfirst : firstSavedWrongOffset input = some index) :
    index < input.val.2.1 ∧
      ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted
        (calendarReferenceRecordAt input index
          ((firstSavedWrongOffset_some_iff_indexed input index).mp hfirst).1) ∧
      calendarReferenceRecordAt input index
          ((firstSavedWrongOffset_some_iff_indexed input index).mp hfirst).1 ∈
        (calendarReferenceRun input).records.take (index + 1) ∧
      (calendarReferenceRecordAt input index
        ((firstSavedWrongOffset_some_iff_indexed input index).mp hfirst).1).input.time.val =
          input.val.1 + index ∧
      (∀ record ∈ (calendarReferenceRun input).records.take index,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record) := by
  let count := input.val.2.1
  have hpositions := (firstSavedWrongOffset_some_iff_code_positions input index).1 hfirst
  rcases hpositions with ⟨hindexCode, hbadCode, hsafeCode⟩
  have hcount : (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2.length = count :=
    calendarRunObservation_recordCount input
  have hindex : index < count := by rw [← hcount]; exact hindexCode
  have hnext : input.val.1 + (index + 1) ≤ p.T :=
    le_trans (Nat.add_le_add_left (Nat.succ_le_of_lt hindex) input.val.1) input.property.1
  let badRecord := calendarReferenceRecordAt input index hindex
  have hbad : savedWrongCode (ReferenceActiveHorizonMeasurability.roundRecordCode badRecord) = true := by
    have hget := calendarCodeAt_referenceRecordAt input index hindex
    have hcode : (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2[index]'hindexCode =
        ReferenceActiveHorizonMeasurability.roundRecordCode badRecord := by
      have hopt := hget
      rw [List.getElem?_eq_getElem hindexCode] at hopt
      exact Option.some.inj hopt
    rw [← hcode]
    exact hbadCode
  have hbadActual :
      ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted badRecord :=
    (savedWrongCode_roundRecord_iff badRecord).1 hbad
  have hrecordInPrefix : badRecord ∈ (calendarReferenceRun input).records.take (index + 1) := by
    change badRecord ∈
      (ReferenceActivePhysicalHorizon.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 count
        input.property.1 input.property.2).records.take (index + 1)
    rw [ReferenceActiveStoppedPrefixCoupling.reference_run_prefix_records
      input.val.2.2.1 input.val.2.2.2.1 input.val.2.2.2.2.1 input.val.2.2.2.2.2
      input.val.1 count input.property.1 input.property.2 (index + 1)
      (Nat.succ_le_of_lt hindex)]
    rw [(ReferenceActiveStoppedPrefixCoupling.reference_successor_equations
      input.val.2.2.1 input.val.2.2.2.1 input.val.2.2.2.2.1 input.val.2.2.2.2.2
      input.val.1 index hnext input.property.2).2]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have htime : badRecord.input.time.val = input.val.1 + index := by
    rfl
  have hsafeCodePrefix : ∀ earlier, earlier < index →
      savedWrongCodeAt (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2
        earlier = false := by
    intro earlier hearlier
    have hearlierCount : earlier < count := by omega
    have hEarlierIndex : earlier <
        (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2.length := by
      rw [hcount]
      exact hearlierCount
    have hnot := hsafeCode earlier hearlier
    have hcode : savedWrongCodeAt
        (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 earlier =
        savedWrongCode ((ReferenceActiveHorizonMeasurability.calendarRunObservation input).2[earlier]) := by
      rw [savedWrongCodeAt_eq_getElem _ earlier hEarlierIndex]
    rw [hcode]
    exact hnot
  have hcodePrefix : savedWrongPrefixCode index
      (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 = false :=
    (savedWrongPrefixCode_false_iff_indexed index
      (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2).2 hsafeCodePrefix
  have hsafeActual := (calendarSavedWrongPrefixCode_false_iff input index).1 (by
    change savedWrongPrefixCode index
      (ReferenceActiveHorizonMeasurability.calendarRunObservation input).2 = false
    exact hcodePrefix)
  exact ⟨hindex, hbadActual, hrecordInPrefix, htime, hsafeActual⟩

/-- A first offset is absent exactly when every actual record of the full
computed run is safe under the saved diagnostic predicate. -/
theorem firstSavedWrongOffset_none_iff
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate)) :
    firstSavedWrongOffset input = none ↔
      ∀ record ∈ (calendarReferenceRun input).records,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
  have hcodeCount := calendarRunObservation_recordCount input
  have hnone : firstSavedWrongOffset input = none ↔ calendarSavedWrongCode input = false := by
    unfold firstSavedWrongOffset calendarSavedWrongCode calendarSavedWrongPrefixCode
      savedWrongPrefixCode
    rw [List.take_of_length_le (Nat.le_of_eq hcodeCount)]
    simp only [List.findIdx?_eq_none_iff, Bool.eq_false_iff]
    constructor
    · intro h hany
      rcases List.any_eq_true.mp hany with ⟨x, hx, hbad⟩
      exact h x hx hbad
    · intro h x hx hbad
      apply h
      exact List.any_eq_true.mpr ⟨x, hx, hbad⟩
  rw [hnone, calendarSavedWrongCode_false_iff]

/-- The first offset facts above are the exact input expected by the accepted
first-bad-boundary theorem. Its result compares predecessor states only
through `index`, while physical traces and rewards include round `index`.
-/
theorem firstSavedWrong_boundary
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    {index : ℕ} (hfirst : firstSavedWrongOffset input = some index) :
    (∃ record ∈ (calendarReferenceRun input).records,
      record.input.time.val = input.val.1 + index ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record) ∧
    (∀ (k : ℕ) (_hk : k ≤ index),
      (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 k (by
          have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
          omega) input.property.2).finalState =
      (ReferenceActivePhysicalHorizon.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 k (by
          have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
          omega) input.property.2).finalState) ∧
    (∀ k, k ≤ index + 1 →
      (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
        input.property.1 input.property.2).physicalTrace.take k =
        ((calendarReferenceRun input).records.map
          ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k) ∧
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 (index + 1) (by
        have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
        omega)
      input.property.2).totalReward =
      (ReferenceActivePhysicalHorizon.run input.val.2.2.1 input.val.2.2.2.1
        input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 (index + 1) (by
          have hindex := (firstSavedWrongOffset_some_iff_indexed input index).mp hfirst |>.1
          omega) input.property.2).totalReward := by
  let hspec := firstSavedWrongOffset_some_spec input hfirst
  simpa [calendarReferenceRun, ReferenceActiveHorizonMeasurability.runOfInput,
    calendarFixedInput] using
    (ReferenceActiveStoppedPrefixCoupling.first_bad_boundary
      input.val.2.2.1 input.val.2.2.2.1 input.val.2.2.2.2.1 input.val.2.2.2.2.2
      input.val.1 input.val.2.1 index input.property.1 input.property.2 hspec.1
      hspec.2.2.2.2 hspec.2.1)

/-- If the first offset is absent, the accepted whole-safe-run theorem gives
equality of the full canonical state, chronological physical trace and reward
for the two existing computations. -/
theorem calendarRun_eq_reference_of_firstSavedWrongOffset_none
    (input : ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate))
    (hnone : firstSavedWrongOffset input = none) :
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
      input.property.1 input.property.2).finalState = (calendarReferenceRun input).finalState ∧
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
      input.property.1 input.property.2).physicalTrace =
      (calendarReferenceRun input).records.map ReferenceActiveStoppedPrefixCoupling.referencePhysical ∧
    (ReferenceActiveStoppedPrefixCoupling.run input.val.2.2.1 input.val.2.2.2.1
      input.val.2.2.2.2.1 input.val.2.2.2.2.2 input.val.1 input.val.2.1
      input.property.1 input.property.2).totalReward = (calendarReferenceRun input).totalReward := by
  have hsafe := (firstSavedWrongOffset_none_iff input).1 hnone
  have hnoneSaved : ∀ record ∈ (calendarReferenceRun input).records,
      ¬ ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record := by
    intro record hrecord hbad
    exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff record).1
      (hsafe record hrecord) hbad
  simpa [calendarReferenceRun, ReferenceActiveHorizonMeasurability.runOfInput,
    calendarFixedInput] using
    (ReferenceActiveStoppedPrefixCoupling.run_eq_reference_of_no_saved_wrong_unique_accepted
      input.val.2.2.1 input.val.2.2.2.1 input.val.2.2.2.2.1 input.val.2.2.2.2.2
      input.val.1 input.val.2.1 input.property.1 input.property.2 hnoneSaved)

end ReferenceSavedWrongUniqueMeasurability

end Bandits.Support
