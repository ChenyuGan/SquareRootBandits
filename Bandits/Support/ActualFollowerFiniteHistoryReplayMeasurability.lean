/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualFollowerFiniteHistoryReplay

/-!
# Joint measurability of the actual finite-history follower replay

The maps below are the literal maps of `ActualFollowerFiniteHistoryReplay`.
Their existing sum, subtype, and continuous carried-state measurable spaces
are retained. The local component lemmas state every measurable-input and
cursor condition; the finite-prefix induction supplies those conditions.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:163-168`.
No execution law or regret assertion is proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions

namespace Bandits.Support.ActualFollowerFiniteHistoryReplayMeasurability

open ActualFollowerFiniteHistoryReplay

variable {p : ActualFollowerFiniteHistoryReplay.Parameters}
  {rate : ActualFollowerFiniteHistoryReplay.RateInput p}

private theorem measurable_of_countable_key {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (f : α → γ)
    (hf : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  intro s hs
  have heq : f ⁻¹' s = key ⁻¹' (key '' (f ⁻¹' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      change f x ∈ s
      rw [hf x y he.symm]
      exact hy
  rw [heq]
  exact hkey (Set.to_countable _).measurableSet

/-- At fixed numerator data, the original begin operation factors through
the original three private draws. -/
theorem measurable_beginBlock (block : Fin (n_boot p))
    (numerators : Fin p.K → ℕ)
    (lowerBound : ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a) :
    Measurable (BootstrapObservedFollower.beginBlock p block numerators lowerBound) := by
  apply measurable_of_countable_key
    (PrivateSourceStreams.privateBlockDrawMap p numerators lowerBound)
    (PrivateSourceStreams.measurable_privateBlockDrawMap p numerators lowerBound)
  intro x y h
  simp only [PrivateSourceStreams.privateBlockDrawMap, Prod.mk.injEq] at h
  simp only [BootstrapObservedFollower.beginBlock, h.1, h.2.1, h.2.2]

/-- Beginning from any fixed original carry uses only an own-stream projection. -/
theorem measurable_beginCode (block : Fin (n_boot p))
    (carry : ActualInitializationRun.FollowerCarry p rate) :
    Measurable (fun own : Own p => beginCode p rate block own carry) := by
  cases carry with
  | bootstrap numerators lowerBound =>
      exact measurable_inl.comp ((measurable_beginBlock block numerators lowerBound).comp
        ((measurable_pi_apply block).comp measurable_fst))
  | declared row activation configuration => exact measurable_const

/-- The literal boundary/carry/begin composition is jointly measurable.
Startup sections are countable; the declared branch preserves every original
incoming configuration coordinate. No measurable structure on a new carry is used. -/
theorem measurable_restart (block next : Fin (n_boot p)) :
    Measurable (fun z : Own p × ReplayFollowerCode p rate block =>
      beginCode p rate next z.1 (carryFromFollowerCode p rate block z.2)) := by
  let split := MeasurableEquiv.prodSumDistrib (Own p)
    (ActualBootstrapObservationCode.StartupCode p block)
    (Fin (M p) × (ReferencePrelaunchFollower.Activation p ×
      FollowerPrepareJointMeasurability.IncomingConfiguration p rate))
  apply split.symm.measurable_comp_iff.mp
  apply measurable_fun_sum
  · change Measurable (fun z : Own p × ActualBootstrapObservationCode.StartupCode p block =>
      beginCode p rate next z.1 (carryFromFollowerCode p rate block (.inl z.2)))
    apply measurable_from_prod_countable_left
    intro startup
    exact measurable_beginCode (rate := rate) next
      (carryFromFollowerCode p rate block (.inl startup))
  · change Measurable (fun z : Own p × (Fin (M p) ×
        (ReferencePrelaunchFollower.Activation p ×
          FollowerPrepareJointMeasurability.IncomingConfiguration p rate)) =>
      beginCode p rate next z.1 (carryFromFollowerCode p rate block (.inr z.2)))
    have heq (z : Own p × (Fin (M p) ×
        (ReferencePrelaunchFollower.Activation p ×
          FollowerPrepareJointMeasurability.IncomingConfiguration p rate))) :
        beginCode p rate next z.1 (carryFromFollowerCode p rate block (.inr z.2)) =
          Sum.inr z.2 := by
      simp only [carryFromFollowerCode,
        ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode,
        ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode,
        ActualInitializationRun.followerCarryOfBoundaryOutput, beginCode,
        incomingOfLocalConfiguration_localConfigurationOfIncoming]
    simp_rw [heq]
    exact measurable_inr.comp measurable_snd

/-- Remove the unused private-coordinate argument from the existing exact
advance reconstruction. This is only an equality of public read formulas;
the unused witness occurs only in this proof application and erases from both
sides. No source-valued measurable map is constructed. -/
theorem observationAdvance_eq_readCode (block : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (rows : CompletePublicTable.CompleteRows p)
    (active : Bool) (privateID : Fin (A_id p))
    (registers : ActualBootstrapObservationCode.RegistersCode p) (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p) :
    BootstrapObservedFollower.observationAdvance p block ids rows active privateID registers time observation =
      ActualBootstrapObservationCode.observationAdvanceFromCode p block
        (ids privateID time, (ActualBootstrapObservationCode.observationPositiveFlag p observation,
          (ActualBootstrapObservationCode.candidateObservationCode p rows privateID time,
            (active, (privateID, (registers, time)))))) := by
  let zero : BootstrapPrivateRoundStreams.Scalar := ⟨0, by norm_num⟩
  let privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p :=
    ((fun _ _ => (zero, zero, zero), zero), (fun _ => zero, fun _ => zero))
  exact ActualBootstrapObservationCode.observationAdvance_reconstruction
    p block ids rows privateCoords active privateID registers time observation

/-- The accepted bootstrap observer is Borel on each fixed startup section.
Its finite key contains original ID reads, candidate bits at the current time,
and the supplied grid value, with the full-block gain preserved. -/
theorem measurable_observeBootstrap_fixed (block : Fin (n_boot p))
    (startup : ActualBootstrapObservationCode.StartupCode p block) (time : Fin p.T)
    (ready : ActualInitializationPhysicalStep.followerAtNextCursor (rate := rate)
      time (.bootstrap startup)) :
    Measurable (fun z : Published p × Fin (D p + 1) =>
      observeBootstrap p rate block startup z.1 time ready z.2) := by
  classical
  let key (z : Published p × Fin (D p + 1)) :=
    (z.1.1, ((fun u : Fin (A_id p) =>
      ActualBootstrapObservationCode.candidateObservationCode p z.1.2 u time), z.2))
  have hkey : Measurable key := by
    have hbits : Measurable (fun z : Published p ×
        Fin (D p + 1) => fun u : Fin (A_id p) =>
          ActualBootstrapObservationCode.candidateObservationCode p z.1.2 u time) :=
      measurable_pi_iff.mpr fun u =>
        (ActualBootstrapObservationCode.measurable_candidateObservationCode_fixed p u time).comp
          (measurable_snd.comp measurable_fst)
    exact (measurable_fst.comp measurable_fst).prodMk (hbits.prodMk measurable_snd)
  apply measurable_of_countable_key key hkey
  intro x y h
  obtain ⟨hids, hbits, hy⟩ := Prod.mk.inj h |>.imp_right (fun h => Prod.mk.inj h)
  have hadvance (u : Fin (A_id p)) (registers : ActualBootstrapObservationCode.RegistersCode p) :
      BootstrapObservedFollower.observationAdvance p block x.1.1 x.1.2 true u registers time
          (ActualInitializationPhysicalStep.observationOfGrid p x.2) =
        BootstrapObservedFollower.observationAdvance p block y.1.1 y.1.2 true u registers time
          (ActualInitializationPhysicalStep.observationOfGrid p y.2) := by
    rw [observationAdvance_eq_readCode, observationAdvance_eq_readCode]
    rw [hids, hy, congrFun hbits u]
  cases hcase : startup.blockCase with
  | inactive =>
      simp only [observeBootstrap, BootstrapObservedFollower.observeOne,
        BootstrapObservedFollower.observeBlockCase, hcase]
  | active held privateID gain registers =>
      have hadvance' := hadvance privateID registers
      rw [hids, hy] at hadvance'
      simp only [observeBootstrap, BootstrapObservedFollower.observeOne,
        BootstrapObservedFollower.observeBlockCase, hcase, hids, hy, hadvance']

/-- Varying startup inputs are handled by countable sections of the existing
startup carrier, with its actual next-cursor proof retained as a subtype. -/
theorem measurable_observeBootstrap_components {Ω : Type*} [MeasurableSpace Ω]
    (block : Fin (n_boot p)) (time : Fin p.T)
    (startup : Ω → ActualBootstrapObservationCode.StartupCode p block)
    (pub : Ω → Published p) (y : Ω → Fin (D p + 1))
    (hstartup : Measurable startup) (hpub : Measurable pub) (hy : Measurable y)
    (ready : ∀ ω, ActualInitializationPhysicalStep.followerAtNextCursor (rate := rate)
      time (.bootstrap (startup ω))) :
    Measurable (fun ω => observeBootstrap p rate block (startup ω) (pub ω)
      time (ready ω) (y ω)) := by
  let Ready := {s : ActualBootstrapObservationCode.StartupCode p block //
    ActualInitializationPhysicalStep.followerAtNextCursor (rate := rate) time (.bootstrap s)}
  have hsection : Measurable (fun z : Ready × (Published p × Fin (D p + 1)) =>
      observeBootstrap p rate block z.1.1 z.2.1 time z.1.2 z.2.2) := by
    apply measurable_from_prod_countable_right
    intro s
    exact measurable_observeBootstrap_fixed block s.1 time s.2
  have hready : Measurable (fun ω => (⟨startup ω, ready ω⟩ : Ready)) := hstartup.subtype_mk
  exact hsection.comp (hready.prodMk (hpub.prodMk hy))

/-- Bootstrap PREPARE and its accepted OBSERVE are jointly Borel on genuine
cursor inputs. All component-map conditions are explicit internal inputs. -/
theorem measurable_bootstrapLocalPair {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : Ω → Published p) (u : Ω → BootstrapPrivateRoundStreams.Scalar)
    (startup : Ω → ActualBootstrapObservationCode.StartupCode p block)
    (y : Ω → Fin (D p + 1))
    (hpub : Measurable pub) (hu : Measurable u)
    (hstartup : Measurable startup) (hy : Measurable y)
    (hs : ∀ ω, ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (.inl (startup ω)))) :
    Measurable (fun ω =>
      let out := localCodeAtScalar p rate i block cursor hc (pub ω) (u ω)
        (.inl (startup ω)) (hs ω) (y ω)
      (out.1, out.2.1)) := by
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hc
  have ready (ω : Ω) : ActualInitializationPhysicalStep.followerAtNextCursor
      (rate := rate) time (.bootstrap (startup ω)) :=
    ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor (rate := rate) hc
      ⟨.bootstrap (startup ω), hs ω⟩
  have harm : Measurable (fun ω => prepareBootstrap p block (startup ω) (pub ω) time (u ω)) :=
    (ActualInitializationPreparationMeasurability.measurable_bootstrapLocalArmFromComponents
      block).comp (hstartup.prodMk
        ((measurable_fst.comp hpub).prodMk (measurable_const.prodMk hu)))
  have hprepared : Measurable (fun ω =>
      (Sum.inl (startup ω, prepareBootstrap p block (startup ω) (pub ω) time (u ω)) :
        ReplayPreparedCode p rate block)) :=
    measurable_inl.comp (hstartup.prodMk harm)
  have hobserved := measurable_observeBootstrap_components block time startup pub y
    hstartup hpub hy ready
  exact hprepared.prodMk hobserved

/-- Declared PREPARE supplies the arm and incoming configuration used by
OBSERVE. The six observation inputs retain their original measurable spaces. -/
theorem measurable_declaredLocalPair {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : Ω → Published p) (u : Ω → BootstrapPrivateRoundStreams.Scalar)
    (fields : Ω → Fin (M p) × (ReferencePrelaunchFollower.Activation p ×
      FollowerPrepareJointMeasurability.IncomingConfiguration p rate))
    (y : Ω → Fin (D p + 1))
    (hpub : Measurable pub) (hfields : Measurable fields) (hy : Measurable y)
    (hs : ∀ ω, ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (.inr (fields ω)))) :
    Measurable (fun ω =>
      let out := localCodeAtScalar p rate i block cursor hc (pub ω) (u ω)
        (.inr (fields ω)) (hs ω) (y ω)
      (out.1, out.2.1)) := by
  let time := ActualPostlaunchFollowerMeasurability.localTime block cursor hc
  let activation := fun ω => (fields ω).2.1
  let incoming := fun ω => (fields ω).2.2
  let row := fun ω => (pub ω).2 (fields ω).1
  have hactivation : Measurable activation := measurable_fst.comp (measurable_snd.comp hfields)
  have hincoming : Measurable incoming := measurable_snd.comp (measurable_snd.comp hfields)
  have hrow : Measurable row :=
    (ActualPostlaunchFollowerMeasurability.measurable_evalCompleteRows_local p).comp
      ((measurable_snd.comp hpub).prodMk (measurable_fst.comp hfields))
  have hvalid (ω : Ω) : (activation ω).val ≤ time.val + 1 := by
    simpa only [activation, time, ActualPostlaunchFollowerMeasurability.localTime,
      ActualInitializationRun.blockTime, ActualInitializationRun.followerAtCursor,
      ActualInitializationRoundMeasurability.followerStateOfCode] using hs ω
  let output := fun ω => FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      (activation ω) (incoming ω) (row ω) time (hvalid ω))
  have houtput : Measurable output :=
    FollowerVaryingActivationMeasurability.measurable_varyingPreparedOutput_atComponents
      rate i activation incoming row (fun _ => time)
      hactivation hincoming hrow measurable_const hvalid
  have hproject : Measurable (fun out :
      FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate => out.2.2) := by
    intro s hs
    change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace
      (FollowerPrepareJointMeasurability.PrepareOutput p rate a)).map (Sigma.mk a))]
      {out | out.2.2 ∈ s}
    rw [MeasurableSpace.measurableSet_iInf]
    intro a
    rw [MeasurableSpace.map_def]
    exact measurable_snd hs
  have hparts := hproject.comp houtput
  have harm : Measurable (fun ω => (output ω).2.2.1) := measurable_fst.comp hparts
  have hpreparedIncoming : Measurable (fun ω => (output ω).2.2.2) :=
    measurable_snd.comp hparts
  have hprepared : Measurable (fun ω =>
      (Sum.inr ((fields ω).1, (activation ω, ((output ω).2.2.1, (output ω).2.2.2))) :
        ReplayPreparedCode p rate block)) :=
    measurable_inr.comp ((measurable_fst.comp hfields).prodMk
      (hactivation.prodMk (harm.prodMk hpreparedIncoming)))
  have hobserved :=
    DeclaredFollowerObservationMeasurability.measurable_observeVaryingCarriedOutputAtComponents
      rate i activation (fun ω => (output ω).2.2.2) row (fun _ => time)
      (fun ω => (output ω).2.2.1) y
      hactivation hpreparedIncoming hrow measurable_const harm hy hvalid
  exact hprepared.prodMk (measurable_inr.comp hobserved)

/-- The literal local operation's produced successor is precisely the right
tag of the existing successor assembly. The accepted bootstrap cursor and the
declared branch both give this identity without an operational default. -/
theorem localCodeAtScalar_successor_inr
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : Published p) (u : BootstrapPrivateRoundStreams.Scalar)
    (state : ReplayFollowerCode p rate block)
    (hs : ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block state))
    (y : Fin (D p + 1)) :
    let out := localCodeAtScalar p rate i block cursor hc pub u state hs y
    Sum.inr (α := Unit) out.2.2 =
      ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput
        rate block (out.1, out.2.1) := by
  cases state <;> rfl

/-- Joint Borel measurability of the literal scalar local operation, on
arbitrary measurable component maps satisfying the real cursor invariant.
These are internal composition inputs, discharged in the replay induction. -/
theorem measurable_localCodeAtScalar {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (pub : Ω → Published p) (u : Ω → BootstrapPrivateRoundStreams.Scalar)
    (state : Ω → ReplayFollowerCode p rate block) (y : Ω → Fin (D p + 1))
    (hpub : Measurable pub) (hu : Measurable u)
    (hstate : Measurable state) (hy : Measurable y)
    (hs : ∀ ω, ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block (state ω))) :
    Measurable (fun ω => localCodeAtScalar p rate i block cursor hc
      (pub ω) (u ω) (state ω) (hs ω) (y ω)) := by
  classical
  let boot : Set Ω := state ⁻¹' Set.range Sum.inl
  have hboot : MeasurableSet boot := measurableSet_range_inl.preimage hstate
  have hpair : Measurable (fun ω =>
      let out := localCodeAtScalar p rate i block cursor hc
        (pub ω) (u ω) (state ω) (hs ω) (y ω)
      (out.1, out.2.1)) := by
    apply measurable_of_restrict_of_restrict_compl hboot
    · let startup (x : boot) : ActualBootstrapObservationCode.StartupCode p block :=
        Equiv.Set.rangeInl _ _ ⟨state x.1, x.2⟩
      have hstartup : Measurable startup :=
        MeasurableEquiv.Set.rangeInl.measurable_toFun.comp
          ((hstate.comp measurable_subtype_coe).subtype_mk)
      have heq (x : boot) : state x.1 = Sum.inl (startup x) := by
        rcases x.2 with ⟨s, he⟩
        simp only [startup, ← he, Equiv.Set.rangeInl_apply_inl]
      have hcursor (x : boot) : ActualInitializationRun.followerAtCursor p rate block cursor
          (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
            (.inl (startup x))) := by
        rw [← heq x]
        exact hs x.1
      have h := measurable_bootstrapLocalPair i block cursor hc
        (fun x : boot => pub x.1) (fun x => u x.1) startup (fun x => y x.1)
        (hpub.comp measurable_subtype_coe) (hu.comp measurable_subtype_coe)
        hstartup (hy.comp measurable_subtype_coe) hcursor
      convert h using 1
      funext x
      simp only [Set.domRestrict_apply, heq x]
    · have hrange (x : ↥bootᶜ) : state x.1 ∈ Set.range Sum.inr := by
        cases he : state x.1 with
        | inl startup => exact False.elim (x.2 ⟨startup, he.symm⟩)
        | inr fields => exact ⟨fields, rfl⟩
      let fields (x : ↥bootᶜ) : Fin (M p) × (ReferencePrelaunchFollower.Activation p ×
          FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :=
        Equiv.Set.rangeInr _ _ ⟨state x.1, hrange x⟩
      have hfields : Measurable fields :=
        MeasurableEquiv.Set.rangeInr.measurable_toFun.comp
          ((hstate.comp measurable_subtype_coe).subtype_mk)
      have heq (x : ↥bootᶜ) : state x.1 = Sum.inr (fields x) := by
        rcases hrange x with ⟨s, he⟩
        simp only [fields, ← he, Equiv.Set.rangeInr_apply_inr]
      have hcursor (x : ↥bootᶜ) : ActualInitializationRun.followerAtCursor p rate block cursor
          (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
            (.inr (fields x))) := by
        rw [← heq x]
        exact hs x.1
      have h := measurable_declaredLocalPair i block cursor hc
        (fun x : ↥bootᶜ => pub x.1) (fun x => u x.1) fields (fun x => y x.1)
        (hpub.comp measurable_subtype_coe) hfields (hy.comp measurable_subtype_coe) hcursor
      convert h using 1
      funext x
      simp only [Set.domRestrict_apply, heq x]
  let out := fun ω => localCodeAtScalar p rate i block cursor hc
    (pub ω) (u ω) (state ω) (hs ω) (y ω)
  have hpartial : Measurable (fun ω => Sum.inr (α := Unit) (out ω).2.2) := by
    have h := (ActualInitializationStepMeasurability.measurable_followerSuccessorCodeFromOutput
      rate block).comp hpair
    convert h using 1
    funext ω
    exact localCodeAtScalar_successor_inr i block cursor hc (pub ω) (u ω)
      (state ω) (hs ω) (y ω)
  have hsuccessor : Measurable (fun ω => (out ω).2.2) :=
    MeasurableEquiv.Set.rangeInr.measurable_toFun.comp
      (hpartial.subtype_mk (h := fun ω => ⟨(out ω).2.2, rfl⟩))
  exact (measurable_fst.comp hpair).prodMk ((measurable_snd.comp hpair).prodMk hsuccessor)

/-- The own-stream version reads just the existing scalar projection for this
fixed calendar cursor. -/
theorem measurable_localCode {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (block : Fin (n_boot p)) (cursor : Nat)
    (hc : cursor < BootstrapObservedFollower.blockLength p block)
    (own : Ω → Own p) (pub : Ω → Published p)
    (state : Ω → ReplayFollowerCode p rate block) (y : Ω → Fin (D p + 1))
    (hown : Measurable own) (hpub : Measurable pub)
    (hstate : Measurable state) (hy : Measurable y)
    (hs : ∀ ω, ActualInitializationRun.followerAtCursor p rate block cursor
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block (state ω))) :
    Measurable (fun ω => localCode p rate i block cursor hc
      (own ω) (pub ω) (state ω) (hs ω) (y ω)) :=
  measurable_localCodeAtScalar i block cursor hc pub
    (fun ω => (own ω).2 (ActualPostlaunchFollowerMeasurability.localTime block cursor hc))
    state y hpub
    ((measurable_pi_apply _).comp (measurable_snd.comp hown)) hstate hy hs

/-- Measurability follows the actual same-block cast or actual boundary
composition in `replayAdvance`. The cursor proofs are the existing subtype
fields, and the calendar branch depends only on the fixed time. -/
theorem measurable_replayAdvance {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (n : Nat) (hnprev : n < p.T) (hnnext : n + 1 < p.T)
    (pub : Ω → Published p) (own : Ω → Own p)
    (previous : Ω → {code : ReplayFollowerCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hnprev⟩) //
      ActualInitializationRun.followerAtCursor p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hnprev⟩)
        (ActualFollowerCalendarContinuity.calendarCursor ⟨n, hnprev⟩)
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate
          (ActualFollowerCalendarContinuity.calendarBlockIndex ⟨n, hnprev⟩) code)})
    (y : Ω → Fin (D p + 1))
    (hpub : Measurable pub) (hown : Measurable own)
    (hprevious : Measurable (fun ω => (previous ω).1)) (hy : Measurable y) :
    Measurable (fun ω => (replayAdvance p rate i (pub ω) (own ω)
      n hnprev hnnext (previous ω) (y ω)).1) := by
  classical
  let t : Fin p.T := ⟨n, hnprev⟩
  let next : Fin p.T := ⟨n + 1, hnnext⟩
  let block := ActualFollowerCalendarContinuity.calendarBlockIndex t
  let cursor := ActualFollowerCalendarContinuity.calendarCursor t
  let hc := ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t
  have hlocal := measurable_localCode i block cursor hc own pub
    (fun ω => (previous ω).1) y hown hpub hprevious hy (fun ω => (previous ω).2)
  have hafter := measurable_snd.comp (measurable_snd.comp hlocal)
  by_cases e : ActualFollowerCalendarContinuity.calendarBlockIndex t =
      ActualFollowerCalendarContinuity.calendarBlockIndex next
  · dsimp only [t, next] at e
    simp only [replayAdvance, dite_eq_left e, Subtype.coe_mk]
    exact (measurable_eq_mp (X := ReplayFollowerCode p rate) e).comp hafter
  · dsimp only [t, next] at e
    simp only [replayAdvance, dite_eq_right e, Subtype.coe_mk]
    exact (measurable_restart (rate := rate) block
      (ActualFollowerCalendarContinuity.calendarBlockIndex next)).comp (hown.prodMk hafter)

/-- Every finite replay prefix is jointly Borel on the whole published
table, the original own streams, and every arbitrary finite grid history. -/
theorem measurable_replayPrefix (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (n : Nat) (hn : n < p.T) :
    Measurable (fun z : Published p × (Own p × HistoryCode p n) =>
      (replayPrefix p rate C_star C_h i z.1 z.2.1 n hn z.2.2).1) := by
  induction n with
  | zero =>
      have he : ActualInitializationRun.firstBlock p =
          ActualFollowerCalendarContinuity.calendarBlockIndex ⟨0, hn⟩ := by
        apply Fin.ext
        exact (Nat.zero_div _).symm
      unfold replayPrefix
      exact (measurable_eq_mp (X := ReplayFollowerCode p rate) he).comp
        ((measurable_beginCode (rate := rate) (ActualInitializationRun.firstBlock p)
          ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i)).comp
            (measurable_fst.comp measurable_snd))
  | succ n ih =>
      have hnprev : n < p.T := Nat.lt_of_succ_lt hn
      let past (z : Published p × (Own p × HistoryCode p (n + 1))) : HistoryCode p n :=
        fun j => z.2.2 ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      have hpast : Measurable past := measurable_pi_iff.mpr fun j =>
        (measurable_pi_apply (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))).comp
          (measurable_snd.comp measurable_snd)
      let previous (z : Published p × (Own p × HistoryCode p (n + 1))) :=
        replayPrefix p rate C_star C_h i z.1 z.2.1 n hnprev (past z)
      have hprevious : Measurable (fun z => (previous z).1) :=
        (ih hnprev).comp (measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk hpast))
      have hy : Measurable (fun z : Published p × (Own p × HistoryCode p (n + 1)) =>
          (z.2.2 ⟨n, Nat.lt_succ_self n⟩).2) :=
        measurable_snd.comp ((measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))).comp
          (measurable_snd.comp measurable_snd))
      unfold replayPrefix
      change Measurable (fun z : Published p × (Own p × HistoryCode p (n + 1)) =>
        (replayAdvance p rate i z.1 z.2.1 n hnprev hn (previous z)
          (z.2.2 ⟨n, Nat.lt_succ_self n⟩).2).1)
      exact measurable_replayAdvance (Ω := Published p × (Own p × HistoryCode p (n + 1)))
        i n hnprev hn
        (fun z => z.1) (fun z => z.2.1) previous
        (fun z => (z.2.2 ⟨n, Nat.lt_succ_self n⟩).2)
        measurable_fst (measurable_fst.comp measurable_snd) hprevious hy

/-- Joint Borel measurability of the accepted literal before-round code.
No source, law, or history-realizability premise is required. -/
theorem follower_replay_code_measurable (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (fun z : Published p × (Own p × HistoryCode p t.val) =>
      (followerReplayCode rate C_star C_h i z.1 z.2.1 t z.2.2).1) :=
  measurable_replayPrefix rate C_star C_h i t.val t.isLt

/-- The current decision is the original prepared arm. A constant typed
feedback value is used only after the complete local code is proved Borel;
the existing arm identity states its independence of that value. -/
theorem follower_grid_decision_measurable (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (fun z : Published p × (Own p × HistoryCode p t.val) =>
      followerGridDecision rate C_star C_h i z.1 z.2.1 t z.2.2) := by
  let before := fun z : Published p × (Own p × HistoryCode p t.val) =>
    followerReplayCode rate C_star C_h i z.1 z.2.1 t z.2.2
  let zero : Fin (D p + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have hlocal := measurable_localCode i
    (ActualFollowerCalendarContinuity.calendarBlockIndex t)
    (ActualFollowerCalendarContinuity.calendarCursor t)
    (ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
    (fun z => z.2.1) (fun z => z.1) (fun z => (before z).1) (fun _ => zero)
    (measurable_fst.comp measurable_snd) measurable_fst
    (follower_replay_code_measurable rate C_star C_h i t) measurable_const
    (fun z => (before z).2)
  have harm := ActualInitializationPreparationMeasurability.measurable_preparedFollowerCodeArm.comp
    (measurable_fst.comp hlocal)
  convert harm using 1
  funext z
  exact followerGridDecision_eq_localCodeArm p rate C_star C_h i z.1 z.2.1 t z.2.2 zero

/-- After the genuine last round, the successor code is jointly Borel,
including an empty strict past when T = 1. -/
theorem follower_replay_after_last_measurable (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : Published p × (Own p × HistoryCode p p.T) =>
      (followerReplayAfterLast p rate C_star C_h i z.1 z.2.1 z.2.2).1) := by
  let last : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  let past (z : Published p × (Own p × HistoryCode p p.T)) : HistoryCode p last.val :=
    fun j => z.2.2 ⟨j.val, Nat.lt_trans j.isLt last.isLt⟩
  have hpast : Measurable past := measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply (⟨j.val, Nat.lt_trans j.isLt last.isLt⟩ : Fin p.T)).comp
      (measurable_snd.comp measurable_snd)
  let before := fun z : Published p × (Own p × HistoryCode p p.T) =>
    followerReplayCode rate C_star C_h i z.1 z.2.1 last (past z)
  have hbefore : Measurable (fun z => (before z).1) :=
    (follower_replay_code_measurable rate C_star C_h i last).comp
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hpast))
  have hy : Measurable (fun z : Published p × (Own p × HistoryCode p p.T) =>
      (z.2.2 last).2) := measurable_snd.comp ((measurable_pi_apply last).comp
        (measurable_snd.comp measurable_snd))
  have hlocal := measurable_localCode i
    (ActualFollowerCalendarContinuity.calendarBlockIndex last)
    (ActualFollowerCalendarContinuity.calendarCursor last)
    (ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength last)
    (fun z => z.2.1) (fun z => z.1) (fun z => (before z).1) (fun z => (z.2.2 last).2)
    (measurable_fst.comp measurable_snd) measurable_fst hbefore hy
    (fun z => (before z).2)
  exact measurable_snd.comp (measurable_snd.comp hlocal)

/-- The literal terminal code is jointly Borel in its existing boundary
output space, retaining clipped boundaries and terminal first declarations. -/
theorem follower_terminal_code_measurable (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : Published p × (Own p × HistoryCode p p.T) =>
      followerTerminalCode rate C_star C_h i z.1 z.2.1 z.2.2) :=
  (ActualInitializationFollowerBoundaryMeasurability.measurable_boundaryOutputFromFollowerCode
    p rate _).comp (follower_replay_after_last_measurable rate C_star C_h i)

/-- The separate original numerator observable is jointly Borel, including
the boundary update whose weights are discarded by a first declaration. -/
theorem follower_terminal_updated_numerators_measurable (rate : RateInput p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : Published p × (Own p × HistoryCode p p.T) =>
      followerTerminalUpdatedNumerators rate C_star C_h i z.1 z.2.1 z.2.2) :=
  (ActualInitializationFollowerBoundaryMeasurability.measurable_boundaryUpdatedNumeratorsCode
    p rate _).comp (follower_replay_after_last_measurable rate C_star C_h i)

end Bandits.Support.ActualFollowerFiniteHistoryReplayMeasurability

end
