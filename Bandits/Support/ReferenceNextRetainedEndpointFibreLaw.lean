/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationKilledJointLaw
public import Bandits.Support.ReferencePostInvocationRetainedEndpointRecurrence

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Retained endpoint and full-vector section law

On both original post-invocation branch lifts, the actual first next call
supplies the retained old-anchor endpoint and its full assignment-vector
fibre law. Splitting only the unused auxiliary block preserves the original
source, private arrays, first vector, used coordinates and first-vector fibre
weight. The weighted real atom identity tests only the physical past; the
vector identities average the fresh block on each fixed old section.

The literal insertion kernel keeps the actual selector, PRE-clear and renewal
flags, fresh-versus-retained endpoint, and absent/stopped Dirac convention.
Global newly inserted-source marginals, the complete sampler graph, renewed
and stopped global projections, call-cell splicing and all-calendar coupling
are outside this module. No manuscript closure is asserted.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:176-215,323-390`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceFirstCollectionLogicalPrefixExtension (noCallAt noCallAt_iff_callAt_none)

namespace Bandits.Support.ReferenceNextRetainedEndpointFibreLaw

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Vector := AssignmentParameterFibreKernel.AssignmentVector
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Outcome (p : ConstructorDimensions.Parameters) := AssignmentParameterFibreKernel.Outcome p

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) := by
  unfold ContinuousLearningRows.TimeControl
  infer_instance

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩
local instance outcomeMeasurableSpace : MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩

private theorem measurable_option_cases {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun x => match o x with | none => f x | some a => g (x, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t : Fin p.T)

local notation "Lift" => BranchLift rate rewards C_star C_h b u t
local notation "Lambda" => branchLaw rate rewards C_star C_h control0 b u t
local notation "O" => branchObservation rate rewards C_star C_h control0 b u t

/-- Survival on `[t+1,q)` followed by the actual invocation at q. -/
def firstNextEvent (q : Fin p.T) : Set Lift :=
  survival rate rewards C_star C_h control0 b u t q.castSucc ∩
    {w | ¬ noCallAt rate rewards C_star C_h q (O q.castSucc w).1.1.1.2}

theorem measurableSet_firstNextEvent (q : Fin p.T) :
    MeasurableSet (firstNextEvent rate rewards C_star C_h control0 b u t q) :=
  (measurableSet_survival rate rewards C_star C_h control0 b u t q.castSucc).inter
    (((ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt
      rate rewards C_star C_h control0 q).preimage
        (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd).compl)

theorem firstNextEvent_iff (q : Fin p.T) (w : Lift) :
    w ∈ firstNextEvent rate rewards C_star C_h control0 b u t q ↔
      (∀ v : Fin p.T, t.val < v.val → v.val < q.val →
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v
          (O q.castSucc w).1.1.1.2 = none) ∧
      ∃ cutoff theta,
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
          (O q.castSucc w).1.1.1.2 = some (cutoff, theta) := by
  change (NoCallBetween rate rewards C_star C_h t q.castSucc _ ∧
    ¬ noCallAt rate rewards C_star C_h q _) ↔ _
  simp only [NoCallBetween, noCallAt_iff_callAt_none, Fin.val_castSucc,
    ← ne_eq, Option.ne_none_iff_exists', Prod.exists]

section EndpointReadout

/-- The generated PRE-call endpoint before any new-episode initialization.
Its accompanying list is still retained in the full observation. -/
def retainedEndpoint (q : Fin p.T) (o : PrefixObservation rate t q.castSucc) : Outcome p :=
  o.2.2.2.map Prod.fst

theorem measurable_retainedEndpoint (q : Fin p.T) :
    Measurable (retainedEndpoint rate (t := t) q) := by
  convert measurable_option_cases _ measurable_snd.snd.snd
    (fun _ : PrefixObservation rate t q.castSucc => (none : Outcome p)) measurable_const
    (fun v : PrefixObservation rate t q.castSucc × (SlowSet p × List (LogicalCell p rate)) => some v.2.1)
    ((measurable_of_countable (some : SlowSet p → Outcome p)).comp measurable_snd.fst) using 1
  funext o
  dsimp only [retainedEndpoint]
  cases o.2.2.2 <;> rfl

end EndpointReadout

section KernelEndpointChoice


/-- A fixed enumeration includes the checked sampler's failure outcome. -/
def outcomeEnumeration (p : ConstructorDimensions.Parameters) :
    Fin (Fintype.card (Outcome p)) ≃ Outcome p := (Fintype.equivFin (Outcome p)).symm

theorem outcome_card_pos (p : ConstructorDimensions.Parameters) :
    0 < Fintype.card (Outcome p) := Fintype.card_pos_iff.mpr ⟨none⟩

/-- These are the actual full-vector sampler's atoms, including null atoms. -/
def fibreAtom (theta : AssignmentParameterFibreKernel.Theta p)
    (i : Fin (Fintype.card (Outcome p))) : ℝ :=
  (AssignmentParameterFibreKernel.fibreMass p theta (outcomeEnumeration p i)).toReal

theorem samplerMass_ne_top (theta : AssignmentParameterFibreKernel.Theta p) (a : Outcome p) :
    AssignmentParameterFibreKernel.fibreMass p theta a ≠ ⊤ :=
  FiniteFibreLift.fibreMass_ne_top _ _ a

theorem fibreAtom_sum (theta : AssignmentParameterFibreKernel.Theta p) :
    ∑ i, fibreAtom theta i = 1 := by
  simp only [fibreAtom]
  rw [(outcomeEnumeration p).sum_comp (fun a =>
    (AssignmentParameterFibreKernel.fibreMass p theta a).toReal)]
  rw [← ENNReal.toReal_sum (fun a _ => samplerMass_ne_top theta a),
    AssignmentParameterFibreKernel.sum_fibreMass_eq_one, ENNReal.toReal_one]

theorem measurable_fibreAtom (i : Fin (Fintype.card (Outcome p))) :
    Measurable (fun theta : AssignmentParameterFibreKernel.Theta p => fibreAtom theta i) :=
  ((AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp
    (measurable_id.prodMk (measurable_const (a := outcomeEnumeration p i)))).ennreal_toReal

/-- A literal fresh categorical sample, reserved for renewed calls. Unlike
the nonrenewed generated endpoint this draw uses the current fresh label. -/
def freshEndpoint (theta : AssignmentParameterFibreKernel.Theta p) (x : Scalar) : Outcome p :=
  outcomeEnumeration p (ContinuousCategorical.sample (outcome_card_pos p)
    (fibreAtom theta) (fibreAtom_sum theta) x)

theorem freshEndpoint_eq_iff (theta : AssignmentParameterFibreKernel.Theta p)
    (x : Scalar) (a : Outcome p) :
    freshEndpoint theta x = a ↔
      ContinuousCategorical.lower (fibreAtom theta) ((outcomeEnumeration p).symm a) ≤ x.val ∧
        x.val < ContinuousCategorical.upper (fibreAtom theta) ((outcomeEnumeration p).symm a) := by
  unfold freshEndpoint
  rw [← Equiv.eq_symm_apply]
  exact ContinuousCategorical.sample_eq_iff (outcome_card_pos p)
    (fun _ => ENNReal.toReal_nonneg) (fibreAtom_sum theta) x _

theorem measurable_freshEndpoint : Measurable (fun v : AssignmentParameterFibreKernel.Theta p × Scalar =>
    freshEndpoint v.1 v.2) := by
  apply measurable_to_countable'
  intro a
  have hl : Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
      ContinuousCategorical.lower (fibreAtom theta) ((outcomeEnumeration p).symm a)) :=
    Finset.measurable_sum _ (fun i _ => measurable_fibreAtom i)
  have hu : Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
      ContinuousCategorical.upper (fibreAtom theta) ((outcomeEnumeration p).symm a)) :=
    Finset.measurable_sum _ (fun i _ => measurable_fibreAtom i)
  convert (measurableSet_le (hl.comp measurable_fst)
    (measurable_subtype_coe.comp measurable_snd)).inter
      (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hu.comp measurable_fst)) using 1
  ext v
  exact freshEndpoint_eq_iff v.1 v.2 a

/-- The branch computation on its small literal coordinate product. -/
def endpointChoice (s : Bool × ((AssignmentParameterFibreKernel.Theta p × Scalar) × Outcome p)) :
    Outcome p := if s.1 then freshEndpoint s.2.1.1 s.2.1.2 else s.2.2

theorem measurable_endpointChoice : Measurable (endpointChoice (p := p)) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    ((measurable_freshEndpoint (p := p)).comp measurable_snd.fst) measurable_snd.snd

end KernelEndpointChoice

section ActualRank

open ReferenceFirstNextInstallationCellFactors
open ReferenceCollectionSamplerChronology

/-- The first-invocation source already produced by the literal branch,
including its first complete-vector insertion. This does not relabel a
later rank as an initializer. -/
def installedFirstSource : Lift → FirstInvocationSource rate rewards C_star C_h t :=
  ReferencePostInvocationRetainedEndpointRecurrence.producedSource rate rewards C_star C_h b u t

theorem installedFirstSource_val (n : Fin (p.T + 1)) (w : Lift) :
    (installedFirstSource rate rewards C_star C_h b u t w).val = (O n w).1.1.1.2 := by
  cases b <;> rfl

/-- The residual seed is the produced cell's actual next set, with the
original branch label: renewed zero, nonrenewed one. -/
theorem produced_seed (w : Lift) :
    postSeed rate (branchTransition rate rewards C_star C_h control0 b u t w) =
      (actualFirstCell rate rewards C_star C_h control0 t
        (installedFirstSource rate rewards C_star C_h b u t w)
        (w.1.2 (t, if b then 0 else 1))).nextSlowSet := by
  exact congrArg LogicalCell.nextSlowSet
    (ReferencePostInvocationRetainedEndpointRecurrence.produced_cell
      rate rewards C_star C_h control0 b u t w)

/-- The incoming payload, cutoff and parameter of the next invocation are
read from its own actual record. Its payload is the produced invocation's
installed payload, so the entire old anchor is inherited on this same path. -/
theorem firstNextEvent_callData (q : Fin p.T) (htq : t.val < q.val)
    (w : Lift) (hw : w ∈ firstNextEvent rate rewards C_star C_h control0 b u t q) :
    let z := installedFirstSource rate rewards C_star C_h b u t w
    ∃ (record : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
      (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val = some record ∧
      record.input.time = q ∧
      record.input.state.coordinator = .collection
        (firstSourceCell rate rewards C_star C_h t z).selected.view.payload ledger saved ∧
      ledger.cutoff = cutoff.val + 1 ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? record.input = some theta ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z.val =
        some (cutoff, theta) ∧
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h q z.val =
        some ledger.freezeAt ∧ t.val < cutoff.val := by
  dsimp only
  let z := installedFirstSource rate rewards C_star C_h b u t w
  obtain ⟨hs, cutoff, theta, hc⟩ :=
    (firstNextEvent_iff rate rewards C_star C_h control0 b u t q w).mp hw
  rw [← installedFirstSource_val] at hc
  obtain ⟨record, hrecord, hselector⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨payload, ledger, saved, hcoord, hcutoff, hparam⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec record cutoff theta).mp hselector
  have hsurv := hw.1
  rw [survival, Set.mem_ofPred_eq, ← installedFirstSource_val] at hsurv
  have hp := (ReferencePostInvocationGeneratedAlignment.firstInvocation_retained_interval
    rate rewards C_star C_h t q.castSucc z hsurv).1 q htq le_rfl record hrecord
  rw [hcoord, ReferenceAssignmentPayloadPersistence.storedPayload_collection] at hp
  have hpay : payload = (firstSourceCell rate rewards C_star C_h t z).selected.view.payload :=
    Option.some.inj hp
  subst payload
  have htime := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val record hrecord).2.2.1
  have hclock := (ReferencePostInvocationGeneratedAlignment.actualRecord_clock
    rate rewards C_star C_h q z.val record hrecord).1
  rw [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclock
  have hcut := hclock.2.1
  have hsigma : (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.sigma = t :=
    ReferencePostInvocationRetainedEndpointRecurrence.producedSource_sigma rate rewards C_star C_h b u t w
  rw [hsigma, hcutoff] at hcut
  have hafter : t.val < cutoff.val := by omega
  obtain ⟨k, _hk, hget, _hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h q z.val record hrecord
  refine ⟨record, cutoff, theta, ledger, saved, hrecord, htime, hcoord, hcutoff, hparam, hc, ?_, hafter⟩
  exact ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h q z.val record (hget ▸ List.getElem_mem k.isLt) htime _ ledger saved hcoord

end ActualRank

section RefreshBlock

/-- The produced residual has its own label. Every later date contributes
both labels. The renewed installation label is deliberately excluded. -/
def refreshCoordinate (b : Bool) (t : Fin p.T)
    (j : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p) : Prop :=
  t.val < j.1.val ∨ (j.1 = t ∧ j.2 = if b then 0 else 1)

abbrev OldAuxiliary (b : Bool) (t : Fin p.T) :=
  {j : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // ¬ refreshCoordinate b t j} → Scalar
abbrev RefreshAuxiliary (b : Bool) (t : Fin p.T) :=
  {j : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // refreshCoordinate b t j} → Scalar

def refreshSplit (b : Bool) (t : Fin p.T) :
    ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p ≃ᵐ
      OldAuxiliary b t × RefreshAuxiliary b t :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => Scalar)
    (refreshCoordinate b t)).trans MeasurableEquiv.prodComm

abbrev oldAuxiliaryLaw (b : Bool) (t : Fin p.T) : Measure (OldAuxiliary b t) :=
  Measure.pi (fun _ => ContinuousControlSlice.scalarLaw)
abbrev refreshAuxiliaryLaw (b : Bool) (t : Fin p.T) : Measure (RefreshAuxiliary b t) :=
  Measure.pi (fun _ => ContinuousControlSlice.scalarLaw)

theorem refreshSplit_measurePreserving : MeasurePreserving (refreshSplit b t)
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
    ((oldAuxiliaryLaw b t).prod (refreshAuxiliaryLaw b t)) := by
  exact (Measure.measurePreserving_swap).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ => ContinuousControlSlice.scalarLaw)
      (refreshCoordinate b t))

/-- These are precisely the two accepted first-insertion kernels. -/
def originalVectorKernel : ProbabilityTheory.Kernel
    (BranchSource rate rewards C_star C_h b u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (Vector p) := match b with
  | false => ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel rate rewards C_star C_h u t control0
  | true => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAssignmentFibreKernel rate rewards C_star C_h u t

instance originalVectorKernel_markov : ProbabilityTheory.IsMarkovKernel
    (originalVectorKernel rate rewards C_star C_h control0 b u t) := by
  cases b
  · exact ReferenceFirstNextInvocationJointLift.nonrenewedVectorKernel_markov
      rate rewards C_star C_h u t control0
  · exact ReferenceFirstCollectionRenewalFibreExtension.renewalAssignmentFibreKernel_markov
      rate rewards C_star C_h u t

def originalSourceLaw : Measure (BranchSource rate rewards C_star C_h b u t) := match b with
  | false => ReferenceFirstNextInvocationJointLift.eventSourceLaw rate rewards C_star C_h u t
  | true => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t

instance originalSourceLaw_finite : IsFiniteMeasure (originalSourceLaw rate rewards C_star C_h b u t) := by
  cases b
  · exact ReferenceFirstNextInvocationJointLift.eventSourceLaw_finite rate rewards C_star C_h u t
  · exact ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite rate rewards C_star C_h u t

theorem branchLaw_compProd : Lambda =
    ((originalSourceLaw rate rewards C_star C_h b u t).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).compProd
        (originalVectorKernel rate rewards C_star C_h control0 b u t) := by
  cases b <;> rfl

/-- The old full-vector fibre weight does not inspect the produced residual
or any future auxiliary coordinate. This retains the same old endpoint. -/
theorem originalVectorKernel_refresh_ext
    (z : BranchSource rate rewards C_star C_h b u t)
    (a a' : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (h : ∀ j, ¬ refreshCoordinate b t j → a j = a' j) :
    originalVectorKernel rate rewards C_star C_h control0 b u t (z, a) =
      originalVectorKernel rate rewards C_star C_h control0 b u t (z, a') := by
  cases b with
  | false =>
      have hp := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
        rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val a a' (by
          intro v hv l
          apply h (v, l)
          simp only [refreshCoordinate, Bool.false_eq_true, ite_false, not_or, not_and]
          exact ⟨by omega, fun he => by subst v; omega⟩)
      have hl := ReferenceFirstNextInvocationJointLift.generatedIncoming_eq_path
        rate rewards C_star C_h u t z a (Fin.last (t.val - u.val))
      have hr := ReferenceFirstNextInvocationJointLift.generatedIncoming_eq_path
        rate rewards C_star C_h u t z a' (Fin.last (t.val - u.val))
      have hdates := ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_dates
        rate rewards C_star C_h u t z.val z.property
      have hd : u.val + (t.val - u.val) = t.val := by omega
      simp only [Fin.val_last, hd] at hl hr
      have he := Option.some.inj (hl.symm.trans ((congrArg Prod.fst hp).trans hr))
      change AssignmentParameterFibreKernel.assignmentParameterFibreKernel p (_, some _) =
        AssignmentParameterFibreKernel.assignmentParameterFibreKernel p (_, some _)
      rw [he]
  | true =>
      have hx := h (t, 1) (by simp [refreshCoordinate])
      change AssignmentParameterFibreKernel.assignmentParameterFibreKernel p
        (_, some (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample
          rate rewards C_star C_h u t z (a (t, 1)))) =
        AssignmentParameterFibreKernel.assignmentParameterFibreKernel p
          (_, some (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample
            rate rewards C_star C_h u t z (a' (t, 1))))
      rw [hx]

/-- Average the actual fresh block after retaining the original source,
old auxiliary coordinates and first inserted vector. Original event and
private-index weights remain inside the accepted source law and kernel. -/
theorem branch_refreshBlock_joint_test
    (Phi : (((BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t) × Vector p) ×
      RefreshAuxiliary b t) → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ x, ‖Phi x‖ ≤ B) :
    (∫ w : Lift, Phi (((w.1.1, (refreshSplit b t w.1.2).1), w.2),
      (refreshSplit b t w.1.2).2) ∂Lambda) =
    ∫ za : BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t,
      ∫ v, ∫ a, Phi ((za, v), a) ∂refreshAuxiliaryLaw b t
        ∂originalVectorKernel rate rewards C_star C_h control0 b u t
          (za.1, (refreshSplit b t).symm (za.2,
            fun _ => ReferenceFirstLiveActualRefreshTestLaw.scalarZero))
      ∂(originalSourceLaw rate rewards C_star C_h b u t).prod (oldAuxiliaryLaw b t) := by
  let mu := originalSourceLaw rate rewards C_star C_h b u t
  let split := refreshSplit b t
  let k := originalVectorKernel rate rewards C_star C_h control0 b u t
  let restore := fun za : BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t =>
    (za.1, split.symm (za.2, fun _ => ReferenceFirstLiveActualRefreshTestLaw.scalarZero))
  have hrestore : Measurable restore :=
    measurable_fst.prodMk (split.symm.measurable.comp (measurable_snd.prodMk measurable_const))
  let k0 := k.comap restore hrestore
  let flat := fun za : BranchSource rate rewards C_star C_h b u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p =>
    ((za.1, (split za.2).1), (split za.2).2)
  have hflat : MeasurePreserving flat
      (mu.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))
      ((mu.prod (oldAuxiliaryLaw b t)).prod (refreshAuxiliaryLaw b t)) :=
    (measurePreserving_prodAssoc mu (oldAuxiliaryLaw b t) (refreshAuxiliaryLaw b t)).symm.comp
      ((MeasurePreserving.id mu).prod (refreshSplit_measurePreserving b t))
  let F := fun x : ((BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t) ×
      RefreshAuxiliary b t) × Vector p => Phi ((x.1.1, x.2), x.1.2)
  have hF : Measurable F := hPhi.comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  let g := fun x : (BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t) ×
      RefreshAuxiliary b t => ∫ v, F (x, v) ∂k0 x.1
  have hg : Measurable g :=
    (hF.stronglyMeasurable.integral_kernel_prod_right'
      (κ := k0.comap Prod.fst measurable_fst)).measurable
  have hgi : Integrable g ((mu.prod (oldAuxiliaryLaw b t)).prod (refreshAuxiliaryLaw b t)) :=
    Integrable.of_bound hg.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
      simpa only [probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := k0 x.1)
          (Filter.Eventually.of_forall fun v => hB ((x.1, v), x.2))))
  have hk (za : BranchSource rate rewards C_star C_h b u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) : k za = k0 (flat za).1 := by
    apply originalVectorKernel_refresh_ext rate rewards C_star C_h control0 b u t
    intro j hj
    change za.2 j = if _ : refreshCoordinate b t j then
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero else za.2 j
    rw [dite_eq_right hj]
  have htest : Measurable (fun w : Lift => F (flat w.1, w.2)) :=
    hF.comp ((hflat.measurable.comp measurable_fst).prodMk measurable_snd)
  have hi : Integrable (fun w : Lift => F (flat w.1, w.2)) Lambda :=
    Integrable.of_bound htest.aestronglyMeasurable B (Filter.Eventually.of_forall fun w => hB _)
  rw [branchLaw_compProd] at hi
  change (∫ w : Lift, F (flat w.1, w.2) ∂Lambda) = _
  rw [branchLaw_compProd, Measure.integral_compProd hi]
  change (∫ za, ∫ v, F (flat za, v) ∂k za ∂mu.prod _) = _
  calc
    _ = ∫ za, g (flat za) ∂mu.prod _ :=
      integral_congr_ae (Filter.Eventually.of_forall fun za => by rw [hk za])
    _ = ∫ x, g x ∂(mu.prod (oldAuxiliaryLaw b t)).prod (refreshAuxiliaryLaw b t) := by
      rw [← hflat.map_eq, integral_map hflat.measurable.aemeasurable hg.aestronglyMeasurable]
    _ = _ := by
      rw [integral_prod _ hgi]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro za
      have hm : Measurable (fun x : RefreshAuxiliary b t × Vector p => Phi ((za, x.2), x.1)) :=
        hPhi.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
      exact integral_integral_swap (f := fun a v => Phi ((za, v), a))
        (μ := refreshAuxiliaryLaw b t) (ν := k0 za)
        (Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => hB _))

section CanonicalRefresh

open ReferenceActualCollectionHiddenRefreshPath
open ReferencePostInvocationRetainedEndpointRecurrence

local instance canonicalSlowSetMeasurableSpace :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := Subtype.instMeasurableSpace

/-- A trigger at the produced date consumes its original residual label.
This is a pointwise address identity, with no measure-invariance assertion. -/
theorem consumedAddress_at_produced_trigger (e n : ℕ) (z : Source p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (htrigger : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e - 1 = t.val) :
    consumedAddress rate rewards C_star C_h e n z hz b t (n - e) le_rfl (.inl ()) =
      (t, if b then 0 else 1) := by
  have hindex := actualCoordinateIndex_trigger rate rewards C_star C_h e n z hz (n - e) le_rfl
  have hj : actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl (.inl ()) =
      (t, 1) := Prod.ext (Fin.ext (hindex.1.trans htrigger)) hindex.2
  unfold consumedAddress
  rw [hj]
  cases b
  · rfl
  · exact Equiv.swap_apply_right (t, 0) (t, 1)

/-- The canonical consumed coordinates are independent coordinates of the
original unused block. The old original coordinates are fixed, without any
claim that swapping labels preserves a fibre-weighted branch measure. -/
theorem refresh_prefixCoordinates_measurePreserving (e n : ℕ) (z : Source p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (htrigger : t.val ≤ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e - 1)
    (old : OldAuxiliary b t) :
    MeasurePreserving (fun a => actualPrefixCoordinates rate rewards C_star C_h e n ⟨z, hz⟩
      (n - e) le_rfl (evaluatorArray b t ((refreshSplit b t).symm (old, a))))
      (refreshAuxiliaryLaw b t) (prefixUniformLaw (n - e)) := by
  let f : (Unit ⊕ (Fin (n - e) ⊕ Fin (n - e))) ↪
      {j : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // refreshCoordinate b t j} :=
    consumedEmbedding rate rewards C_star C_h e n z hz b t htrigger (n - e) le_rfl
  have hi := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : {j : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // refreshCoordinate b t j} =>
      ContinuousControlSlice.scalarLaw) (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hselection : MeasurePreserving (fun a : RefreshAuxiliary b t => fun i => a (f i))
      (refreshAuxiliaryLaw b t)
      (Measure.pi (fun _ : Unit ⊕ (Fin (n - e) ⊕ Fin (n - e)) => ContinuousControlSlice.scalarLaw)) := by
    refine ⟨measurable_pi_iff.mpr (fun _ => measurable_pi_apply _), ?_⟩
    have h := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
      (fun i => (measurable_pi_apply (f i)).aemeasurable) (hi.precomp f.injective)
    have hmarginal (i : Unit ⊕ (Fin (n - e) ⊕ Fin (n - e))) :
        (refreshAuxiliaryLaw b t).map (fun a => a (f i)) = ContinuousControlSlice.scalarLaw :=
      (measurePreserving_eval (fun _ => ContinuousControlSlice.scalarLaw) (f i)).map_eq
    simpa only [hmarginal] using h
  have houter := measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ (Fin (n - e) ⊕ Fin (n - e)) => ContinuousControlSlice.scalarLaw)
  have hinner := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin (n - e) ⊕ Fin (n - e) => ContinuousControlSlice.scalarLaw)
  have hsplit := ((measurePreserving_piUnique (fun _ : Unit => ContinuousControlSlice.scalarLaw)).prod
    hinner).comp (houter.comp hselection)
  have hcombine := (measurePreserving_arrowProdEquivProdArrow Scalar Scalar (Fin (n - e))
    (fun _ => ContinuousControlSlice.scalarLaw) (fun _ => ContinuousControlSlice.scalarLaw)).symm
  have hresult := ((MeasurePreserving.id ContinuousControlSlice.scalarLaw).prod hcombine).comp hsplit
  let extract := fun a : RefreshAuxiliary b t => actualPrefixCoordinates rate rewards C_star C_h e n
    ⟨z, hz⟩ (n - e) le_rfl (evaluatorArray b t ((refreshSplit b t).symm (old, a)))
  have hentry (a : RefreshAuxiliary b t) (i : Unit ⊕ (Fin (n - e) ⊕ Fin (n - e))) :
      evaluatorArray b t ((refreshSplit b t).symm (old, a))
        (actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl i) = a (f i) := by
    change (if h : refreshCoordinate b t (consumedAddress rate rewards C_star C_h e n z hz b t
      (n - e) le_rfl i) then a ⟨_, h⟩ else old ⟨_, h⟩) = _
    have hj : refreshCoordinate b t
        (consumedAddress rate rewards C_star C_h e n z hz b t (n - e) le_rfl i) :=
      consumedAddress_unused rate rewards C_star C_h e n z hz b t htrigger (n - e) le_rfl i
    rw [dite_eq_left hj]
    rfl
  have hextract : MeasurePreserving extract (refreshAuxiliaryLaw b t) (prefixUniformLaw (n - e)) := by
    convert hresult using 1
    · funext a
      exact Prod.ext (hentry a (.inl ()))
        (funext fun i => Prod.ext (hentry a (.inr (.inl i))) (hentry a (.inr (.inr i))))
    · rfl
  exact hextract

/-- Endpoint atoms after fixing the old array coordinates. -/
theorem refresh_sampledArrayPath_atom (e n : ℕ) (z : Source p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (htrigger : t.val ≤ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e - 1)
    (old : OldAuxiliary b t) (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    refreshAuxiliaryLaw b t {a | sampledArrayPath rate rewards C_star C_h e n z hz
      (n - e) le_rfl (evaluatorArray b t ((refreshSplit b t).symm (old, a))) (Fin.last (n - e)) = U} =
    ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
      {a | sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl a (Fin.last (n - e)) = U} := by
  let S := {c : DeferredRefreshUniformEvaluator.PrefixCoordinates (n - e) |
    sampledPath rate rewards C_star C_h e n z hz (n - e) le_rfl c (Fin.last (n - e)) = U}
  have hS : MeasurableSet S := by
    let B : Set (Fin (n - e + 1) → CanonicalOrientedSetLaw.SlowSet p.K p.m) := {V | V (Fin.last (n - e)) = U}
    change MeasurableSet (sampledPath rate rewards C_star C_h e n z hz (n - e) le_rfl ⁻¹' B)
    exact (measurable_sampledPath rate rewards C_star C_h e n z hz (n - e) le_rfl) MeasurableSet.of_discrete
  have hfix := refresh_prefixCoordinates_measurePreserving rate rewards C_star C_h b t e n z hz htrigger old
  have hfull : MeasurePreserving (actualPrefixCoordinates rate rewards C_star C_h e n ⟨z, hz⟩ (n - e) le_rfl)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) (prefixUniformLaw (n - e)) :=
    ⟨(measurable_actualPrefixCoordinates_joint rate rewards C_star C_h e n (n - e) le_rfl).comp
      ((measurable_const (a := (⟨z, hz⟩ : PrefixSource rate rewards C_star C_h e n))).prodMk measurable_id),
      actualPrefixCoordinates_map rate rewards C_star C_h e n z hz (n - e) le_rfl⟩
  exact (hfix.measure_preimage hS.nullMeasurableSet).trans (hfull.measure_preimage hS.nullMeasurableSet).symm

local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "records " z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h

private theorem canonical_cutoff_record (e n : ℕ) (z : Source p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n) :
    recordAt (cutoffDate rate rewards C_star C_h e n z hz) z =
      some ((records z)[e]'(collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose) := by
  have he := (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose
  change (if start z ≤ start z + e then (records z)[start z + e - start z]? else none) = _
  rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem he]

private theorem continuing_not_cutoff (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (h : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have hp : (ReferenceActivePhysicalStep.prepare r.input).coordinator = r.output.preparation.coordinator := by
    rw [r.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [hp]
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at h
  cases hc : r.output.preparation.coordinator <;> simp only [hc] at h ⊢
  next r q base outcome => cases outcome <;> simp_all only

private theorem canonical_window_collection (e n : ℕ) (z : Source p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (q : Fin p.T) (htq : t.val < q.val) (s : FirstInvocationSource rate rewards C_star C_h t)
    (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z)
    (k : ℕ) (hk : e + k < n) :
    z ∈ collectionDateDomain rate rewards C_star C_h ⟨start z + e + k, by omega⟩ := by
  have hafter := produced_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have hepos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  induction k with
  | zero =>
      let v := cutoffDate rate rewards C_star C_h e n z hz
      have hn := hcall v hafter (by change start z + e < q.val; omega)
      rcases ReferencePostInvocationNoncallGeometry.noncall_phase_coverage
          rate rewards C_star C_h v z (by change start z < start z + e; omega) hn with hl | hc
      · have hr := (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec
          rate rewards C_star C_h v ⟨z, hl⟩).1
        have heq := Option.some.inj (hr.symm.trans (canonical_cutoff_record rate rewards C_star C_h e n z hz))
        have hn := continuing_not_cutoff rate _
          (ReferencePostInvocationGeneratedAlignment.continuingRecord_frame
            rate rewards C_star C_h v ⟨z, hl⟩).choose_spec.choose_spec.choose_spec.choose_spec.2.1
        rw [heq, (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose_spec.choose_spec.choose_spec.choose_spec.2.1]
          at hn
        cases hn
      · exact hc
  | succ k ih =>
      let v : Fin p.T := ⟨start z + e + k, by omega⟩
      let v' : Fin p.T := ⟨start z + e + (k + 1), by omega⟩
      have hc : z ∈ collectionDateDomain rate rewards C_star C_h v := ih (by omega)
      have hv := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
      obtain ⟨ledger, saved, hout⟩ :=
        ReferencePostInvocationGeneratedAlignment.collectionRecord_output rate rewards C_star C_h v ⟨z, hc⟩
      have hn := hcall v' (by dsimp only [v']; omega) (by change start z + e + (k + 1) < q.val; omega)
      rcases ReferencePostInvocationNoncallGeometry.noncall_phase_coverage
          rate rewards C_star C_h v' z (by dsimp only [v']; omega) hn with hl | hc'
      · obtain ⟨r, owned, base, started, hin, _⟩ :=
          ReferencePostInvocationGeneratedAlignment.continuingRecord_frame rate rewards C_star C_h v' ⟨z, hl⟩
        have hv' := (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec
          rate rewards C_star C_h v' ⟨z, hl⟩).1
        have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
          (ReferencePostInvocationGeneratedAlignment.actualRecord_adjacent rate rewards C_star C_h v v'
            (by dsimp only [v, v']; omega) z _ _ hv hv')
        rw [hin, hout] at hadj
        cases hadj
      · exact hc'

/-- Canonical trigger witnesses on this one call-free source are unique.
No equality between arbitrary existential witnesses is assumed. -/
theorem canonical_trigger_unique (e e' n : ℕ) (z : Source p)
    (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)
    (hz' : z ∈ collectionPrefixCell rate rewards C_star C_h e' n)
    (q : Fin p.T) (htq : t.val < q.val) (s : FirstInvocationSource rate rewards C_star C_h t)
    (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z) : e = e' := by
  suffices ∀ (i j : ℕ), z ∈ collectionPrefixCell rate rewards C_star C_h i n →
      z ∈ collectionPrefixCell rate rewards C_star C_h j n → ¬ i < j by
    have h1 := this e e' hz hz'
    have h2 := this e' e hz' hz
    omega
  intro i j hi hj hij
  let v : Fin p.T := ⟨start z + j - 1, by have := hj.1; omega⟩
  let v' := cutoffDate rate rewards C_star C_h j n z hj
  have hc : z ∈ collectionDateDomain rate rewards C_star C_h v := by
    have hh := canonical_window_collection rate rewards C_star C_h (t := t) i n z hi q htq s hs
      hdate hcall (j - 1 - i) (by have := hj.1; omega)
    convert hh using 1
    congr 1
    apply Fin.ext
    dsimp only [v]
    omega
  have hv := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
  obtain ⟨ledger, saved, hout⟩ :=
    ReferencePostInvocationGeneratedAlignment.collectionRecord_output rate rewards C_star C_h v ⟨z, hc⟩
  obtain ⟨he, r, owned, base, hin, _⟩ := collectionPrefixCell_live rate rewards C_star C_h j n z hj
  have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
    (ReferencePostInvocationGeneratedAlignment.actualRecord_adjacent rate rewards C_star C_h v v'
      (by dsimp only [v, v', cutoffDate]; omega) z _ _ hv
      (canonical_cutoff_record rate rewards C_star C_h j n z hj))
  rw [hin, hout] at hadj
  cases hadj

end CanonicalRefresh

end RefreshBlock

section InstallationKernel


variable (q : Fin p.T)

abbrev NextInput (rate : ReferenceActivePhysicalStep.RateInput p) (t q : Fin p.T) :=
  PrefixObservation rate t q.castSucc × (Scalar × Scalar)

/-- The incoming ledger decides renewal before the current assignment draw. -/
def renewalFlag (o : PrefixObservation rate t q.castSucc) : Bool :=
  (ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h q o.1.1.1.2).any
    (fun g => decide (g ≤ q.val + 1))

theorem measurable_renewalFlag : Measurable (renewalFlag rate rewards C_star C_h (t := t) q) := by
  have hg := (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_oldFreezeAt?
    rate rewards C_star C_h q).comp
      (measurable_fst.fst.fst.snd : Measurable (fun o : PrefixObservation rate t q.castSucc => o.1.1.1.2))
  convert measurable_option_cases _ hg
    (fun _ : PrefixObservation rate t q.castSucc => false) measurable_const
    (fun v : PrefixObservation rate t q.castSucc × ℕ => decide (v.2 ≤ q.val + 1))
    ((measurable_of_countable (fun g : ℕ => decide (g ≤ q.val + 1))).comp measurable_snd) using 1
  funext o
  dsimp only [renewalFlag, Function.comp_apply]
  cases ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h q o.1.1.1.2 <;> rfl

/-- PRE overflow alone disables analytical insertion. The physical protocol
still continues, and this flag does not inspect POST overflow. -/
def preClearFlag (o : PrefixObservation rate t q.castSucc) : Bool :=
  o.2.2.1.any (fun S => !S.overflow)

theorem measurable_preClearFlag : Measurable (preClearFlag rate (t := t) q) := by
  convert measurable_option_cases _ measurable_snd.snd.fst
    (fun _ : PrefixObservation rate t q.castSucc => false) measurable_const
    (fun v : PrefixObservation rate t q.castSucc × RecordedQueueRun.RunState p.K => !v.2.overflow)
    ((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => !S.overflow)).comp measurable_snd)
      using 1
  funext o
  dsimp only [preClearFlag]
  cases o.2.2.1 <;> rfl

/-- Vary only the analytical array; retain the original source and first vector. -/
def withAuxiliary (w : Lift) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) : Lift :=
  ((w.1.1, a), w.2)

theorem withAuxiliary_source (n : Fin (p.T + 1)) (w : Lift)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    (O n (withAuxiliary rate rewards C_star C_h b u t w a)).1.1.1.2 = (O n w).1.1.1.2 := by
  cases b <;> rfl

/-- Resample exactly the unused coordinates, retaining both original sources,
the old coordinates and the first inserted vector. -/
def refreshAgain (w : Lift) (a : RefreshAuxiliary b t) : Lift :=
  withAuxiliary rate rewards C_star C_h b u t w
    ((refreshSplit b t).symm ((refreshSplit b t w.1.2).1, a))

theorem measurable_refreshAgain :
    Measurable (fun wa : Lift × RefreshAuxiliary b t =>
      refreshAgain rate rewards C_star C_h b u t wa.1 wa.2) :=
  (measurable_fst.fst.fst.prodMk ((refreshSplit b t).symm.measurable.comp
    (((refreshSplit b t).measurable.fst.comp measurable_fst.fst.snd).prodMk measurable_snd))).prodMk
      measurable_fst.snd

/-- The original fibre-weighted law is stationary under refreshing only its
unused block. This is not a label-swap assertion about that weighted law. -/
theorem refreshAgain_integral (f : Lift → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ w, ‖f w‖ ≤ B) :
    (∫ w, ∫ a, f (refreshAgain rate rewards C_star C_h b u t w a)
      ∂refreshAuxiliaryLaw b t ∂Lambda) = ∫ w, f w ∂Lambda := by
  let restore := fun x : (((BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t) × Vector p) ×
      RefreshAuxiliary b t) => ((x.1.1.1, (refreshSplit b t).symm (x.1.1.2, x.2)), x.1.2)
  have hr : Measurable restore :=
    (measurable_fst.fst.fst.prodMk ((refreshSplit b t).symm.measurable.comp
      (measurable_fst.fst.snd.prodMk measurable_snd))).prodMk measurable_fst.snd
  let F := f ∘ restore
  have hF : Measurable F := hf.comp hr
  let avg := fun x : (BranchSource rate rewards C_star C_h b u t × OldAuxiliary b t) × Vector p =>
    ∫ a, F (x, a) ∂refreshAuxiliaryLaw b t
  have ha : Measurable avg := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hb (x) : ‖avg x‖ ≤ B := by
    simpa only [avg, F, Function.comp_apply, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := refreshAuxiliaryLaw b t)
        (Filter.Eventually.of_forall fun a => hB (restore (x, a))))
  have hleft := branch_refreshBlock_joint_test rate rewards C_star C_h control0 b u t F hF B
    (fun x => hB (restore x))
  have hright := branch_refreshBlock_joint_test rate rewards C_star C_h control0 b u t
    (fun x => avg x.1) (ha.comp measurable_fst) B (fun x => hb x.1)
  calc
    _ = ∫ w : Lift, avg ((w.1.1, (refreshSplit b t w.1.2).1), w.2) ∂Lambda := rfl
    _ = _ := by
      rw [hright]
      simp only [integral_const, probReal_univ, one_smul]
      rw [← hleft]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        dsimp only [F, Function.comp_apply, restore]
        rw [Prod.mk.eta, (refreshSplit b t).symm_apply_apply]

/-- The actual retained generated endpoint is the canonical old-anchor path
on this very inserted physical source. Both branch labels are literal;
renewal reads its unused label zero for the produced residual. -/
theorem actual_nextNonrenewed_retained (htq : t.val < q.val) (w : Lift)
    (hw : w ∈ firstNextEvent rate rewards C_star C_h control0 b u t q)
    (hclear : preClearFlag rate (t := t) q (O q.castSucc w) = true)
    (hnr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = false) :
    let z := (O q.castSucc w).1.1.1.2
    ∃ (e n : ℕ) (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (hz : z ∈ ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell rate rewards C_star C_h e n),
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z = some (cutoff, theta) ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n = q.val ∧
      theta.1 = (RecordedCorrectedWindow.actualPrefixSamplerMass p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceActualCollectionNonrenewedEndpointFibreJoin.collectionQueue_sourceCap rate)
        (ReferenceActualCollectionHiddenRefreshPath.collectionWord rate rewards C_star C_h e n z hz) e n
        (ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell_trigger_positive
          rate rewards C_star C_h e n z hz) hz.1
        (ReferenceActualCollectionHiddenRefreshPath.collectionWord_bound rate rewards C_star C_h e n z hz)).weight ∧
      theta.2 = (ReferenceActualCollectionHiddenRefreshPath.oldPayload rate rewards C_star C_h e n z hz).anchor ∧
      ReferenceActualCollectionHiddenRefreshPath.oldPayload rate rewards C_star C_h e n z hz =
        (firstSourceCell rate rewards C_star C_h t
          (installedFirstSource rate rewards C_star C_h b u t w)).selected.view.payload ∧
      ReferenceActualCollectionHiddenRefreshPath.cutoffDate rate rewards C_star C_h e n z hz = cutoff ∧
      prefixNumerical rate rewards C_star C_h q.castSucc z =
        some (ReferenceActualCollectionHiddenRefreshPath.collectionState rate rewards C_star C_h e n z hz n) ∧
      t.val ≤ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e - 1 ∧
      ∀ a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p,
        retainedEndpoint rate (t := t) q
          (O q.castSucc (withAuxiliary rate rewards C_star C_h b u t w a)) =
          some (ReferenceActualCollectionHiddenRefreshPath.sampledArrayPath rate rewards C_star C_h e n z hz
            (n - e) le_rfl (ReferencePostInvocationRetainedEndpointRecurrence.evaluatorArray b t a)
            (Fin.last (n - e))) := by
  dsimp only
  let z := (O q.castSucc w).1.1.1.2
  obtain ⟨r, cutoff, theta, ledger, saved, hr, ht, hcoord, _hcut, _hp, hc, hf, _hafter⟩ :=
    firstNextEvent_callData rate rewards C_star C_h control0 b u t q htq w hw
  rw [installedFirstSource_val rate rewards C_star C_h control0 b u t q.castSucc w] at hr hc hf
  have hlt : q.val + 1 < ledger.freezeAt := by
    have hn : ¬ ledger.freezeAt ≤ q.val + 1 := by
      simpa only [renewalFlag, hf, Option.any_some, decide_eq_false_iff_not] using hnr
    exact lt_of_not_ge hn
  have hcall : ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
      rate rewards C_star C_h q z := by
    refine ⟨?_, r, hr, ?_⟩
    · rw [hc]
      rfl
    · rw [hcoord, ht]
      exact hlt
  have hnum : prefixNumerical rate rewards C_star C_h q.castSucc z = (O q.castSucc w).2.2.1 := by
    cases b <;> rfl
  have hread : ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h q.val z = some o ∧ o.2.1 = false := by
    cases hn : (O q.castSucc w).2.2.1 with
    | none => simp only [preClearFlag, hn, Option.any_none, Bool.false_eq_true] at hclear
    | some S =>
        have hov : S.overflow = false := by
          cases ho : S.overflow with
          | false => rfl
          | true => simp only [preClearFlag, hn, Option.any_some, ho, Bool.not_true,
              Bool.false_eq_true] at hclear
        rw [hn] at hnum
        refine ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout S, ?_, hov⟩
        have hm := congrArg (Option.map ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout) hnum
        simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
          prefixNumerical, Option.map_map, Function.comp_def, Option.map_some, Fin.val_castSucc] using hm
  have hbetween := hw.1
  rw [survival, Set.mem_ofPred_eq, branchObservation_source] at hbetween
  dsimp only [z] at hcall hread
  rw [branchObservation_source] at hcall hread
  obtain ⟨e, n, cutoff, theta, hz, hc, hd, hm, ha, hp, hnum, htrigger, _hret, _hinj, _hunused⟩ :=
    ReferencePostInvocationRetainedEndpointRecurrence.retained_endpoint
      rate rewards C_star C_h control0 b u t q htq w hbetween hcall hread
  have hcutoff : ReferenceActualCollectionHiddenRefreshPath.cutoffDate
      rate rewards C_star C_h e n _ hz = cutoff := by
    obtain ⟨e', n', r', cutoff', theta', hz', hr', hc', hd', ledger', saved', hcoord', hcut'⟩ :=
      ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall_prefixCell
        rate rewards C_star C_h q _ hcall hread
    have hn : n' = n := by omega
    subst n'
    have he := canonical_trigger_unique rate rewards C_star C_h (t := t) e' e n _ hz' hz q htq
      (installedFirstSource rate rewards C_star C_h b u t w)
      (ReferencePostInvocationRetainedEndpointRecurrence.producedSource_val
        rate rewards C_star C_h control0 b u t w) hd hbetween
    subst e'
    have hselector : ReferenceFirstCollectionSamplerCall.collectionCallAt r' =
        some (cutoff', theta') := by
      have h := hc'
      change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q _).bind
        ReferenceFirstCollectionSamplerCall.collectionCallAt = some (cutoff', theta') at h
      rw [hr'] at h
      exact h
    obtain ⟨payload, ledger, saved, hcoord, hcut, _hparam⟩ :=
      (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r' cutoff' theta').mp hselector
    have hledger : ledger' = ledger :=
      (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj (hcoord'.symm.trans hcoord)).2.1
    have hvalue := congrArg (fun c : Fin p.T × AssignmentParameterFibreKernel.Theta p => c.1.val)
      (Option.some.inj (hc'.symm.trans hc))
    change cutoff'.val = cutoff.val at hvalue
    rw [hledger] at hcut'
    apply Fin.ext
    change ReferenceCompletePhysicalHistory.physicalStart rate _ rewards C_star C_h + e = cutoff.val
    omega
  rw [branchObservation_source]
  refine ⟨e, n, cutoff, theta, hz, hc, hd, hm, ha, hp, hcutoff, hnum, htrigger, ?_⟩
  intro a
  let w' := withAuxiliary rate rewards C_star C_h b u t w a
  have hs : insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w') =
      insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w) := by
    cases b <;> rfl
  obtain ⟨e', n', cutoff', theta', hz', _hc', hd', _hm', _ha', _hp', _hnum', _htr', hret', _⟩ :=
    ReferencePostInvocationRetainedEndpointRecurrence.retained_endpoint
      rate rewards C_star C_h control0 b u t q htq w'
      (by rw [hs]; exact hbetween) (by rw [hs]; exact hcall) (by rw [hs]; exact hread)
  simp only [hs] at hz' hd' hret'
  have hn : n' = n := by omega
  subst n'
  have he := canonical_trigger_unique rate rewards C_star C_h (t := t) e' e n _ hz' hz q htq
    (installedFirstSource rate rewards C_star C_h b u t w)
    (ReferencePostInvocationRetainedEndpointRecurrence.producedSource_val
      rate rewards C_star C_h control0 b u t w) hd hbetween
  subst e'
  exact hret'

/-- On each fixed original-source/first-vector section, average the genuine
unused block. This includes the failure atom and every null successful atom;
no future decoding event is imposed. -/
theorem actual_nextNonrenewed_refresh_atoms (htq : t.val < q.val) (w : Lift)
    (hw : w ∈ firstNextEvent rate rewards C_star C_h control0 b u t q)
    (hclear : preClearFlag rate (t := t) q (O q.castSucc w) = true)
    (hnr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = false) :
    ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
        (O q.castSucc w).1.1.1.2 = some (cutoff, theta) ∧
      AssignmentParameterFibreKernel.fibreMass p theta none = 0 ∧
      ∀ (old : OldAuxiliary b t) (A : Outcome p),
        refreshAuxiliaryLaw b t {a | retainedEndpoint rate (t := t) q
          (O q.castSucc (withAuxiliary rate rewards C_star C_h b u t w
            ((refreshSplit b t).symm (old, a)))) = A} =
          AssignmentParameterFibreKernel.fibreMass p theta A := by
  obtain ⟨e, n, cutoff, theta, hz, hc, _hd, hm, ha, _hp, _hcutoff, _hnum, htrigger, hret⟩ :=
    actual_nextNonrenewed_retained rate rewards C_star C_h control0 b u t q htq w hw hclear hnr
  let z := (O q.castSucc w).1.1.1.2
  let L := ReferenceActualCollectionHiddenRefreshPath.collectionWord rate rewards C_star C_h e n z hz
  let P := ReferenceActualCollectionHiddenRefreshPath.oldPayload rate rewards C_star C_h e n z hz
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have he := ReferenceActualCollectionHiddenRefreshPath.collectionPrefixCell_trigger_positive
    rate rewards C_star C_h e n z hz
  have hb := ReferenceActualCollectionHiddenRefreshPath.collectionWord_bound rate rewards C_star C_h e n z hz
  let cap := ReferenceActualCollectionNonrenewedEndpointFibreJoin.collectionQueue_sourceCap rate
  let mass := RecordedCorrectedWindow.actualPrefixSamplerMass p Q cap L e n he hz.1 hb
  have htheta : theta = (mass.weight, P.anchor) := Prod.ext hm ha
  have hsampler (v : Vector p) : AssignmentParameterFibreKernel.successfulSlowSet p theta v =
      some (CorrectedAssignmentVector.correctedSlowSampler p Q cap L e n he hz.1 hb P.anchor P.anchor_pos v) := by
    rw [htheta]
    exact CheckedAssignmentSample.actualCorrected_successfulSlowSet_eq_sampler p Q cap L e n he hz.1 hb
      P.anchor P.anchor_pos v
  have hnone : AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
    change ContinuousControlSlice.assignmentLaw p.K {v | _ = none} = 0
    simp_rw [hsampler]
    simp only [reduceCtorEq, Set.ofPred_false, measure_empty]
  refine ⟨cutoff, theta, hc, hnone, ?_⟩
  intro old A
  cases A with
  | none =>
      simp_rw [hret]
      simp only [reduceCtorEq, Set.ofPred_false, measure_empty, hnone]
  | some U =>
      simp_rw [hret, Option.some.injEq]
      rw [refresh_sampledArrayPath_atom rate rewards C_star C_h b t e n z hz htrigger old U]
      have hfibre : AssignmentParameterFibreKernel.fibreMass p theta (some U) =
          ENNReal.ofReal (CorrectedAssignmentVector.slowFibreMass p Q cap L e n he hz.1 hb
            P.anchor P.anchor_pos U) := by
        rw [htheta]
        exact CheckedAssignmentSample.actualCorrected_checkedSlow_fibreMass p Q cap L e n he hz.1 hb
          P.anchor P.anchor_pos U
      have hendpoint : (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).real
          {a | ReferenceActualCollectionHiddenRefreshPath.sampledArrayPath rate rewards C_star C_h e n z hz
            (n - e) le_rfl a (Fin.last (n - e)) = U} =
          CorrectedAssignmentVector.slowFibreMass p Q cap L e n he hz.1 hb P.anchor P.anchor_pos U :=
        ReferenceActualCollectionEnabledPrefixEndpoint.actual_collection_endpoint_atom
          rate rewards C_star C_h e n z hz U
      exact (MeasureTheory.ofReal_measureReal).symm.trans ((congrArg ENNReal.ofReal hendpoint).trans hfibre.symm)

/-- The retained, PRE-clear, immediate corrected-call event. -/
def retainedNextEvent : Set Lift :=
  firstNextEvent rate rewards C_star C_h control0 b u t q ∩
    {w | preClearFlag rate (t := t) q (O q.castSucc w) = true ∧
      renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = false}

theorem measurableSet_retainedNextEvent :
    MeasurableSet (retainedNextEvent rate rewards C_star C_h control0 b u t q) :=
  (measurableSet_firstNextEvent rate rewards C_star C_h control0 b u t q).inter
    ((measurableSet_eq_fun ((measurable_preClearFlag rate (t := t) q).comp
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)) measurable_const).inter
      (measurableSet_eq_fun ((measurable_renewalFlag rate rewards C_star C_h (t := t) q).comp
        (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)) measurable_const))

theorem withAuxiliary_retainedNextEvent_iff (w : Lift)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    withAuxiliary rate rewards C_star C_h b u t w a ∈
      retainedNextEvent rate rewards C_star C_h control0 b u t q ↔
      w ∈ retainedNextEvent rate rewards C_star C_h control0 b u t q := by
  have he : withAuxiliary rate rewards C_star C_h b u t w a ∈
      firstNextEvent rate rewards C_star C_h control0 b u t q ↔
      w ∈ firstNextEvent rate rewards C_star C_h control0 b u t q := by
    rw [firstNextEvent_iff, firstNextEvent_iff, withAuxiliary_source]
  have hn : (O q.castSucc (withAuxiliary rate rewards C_star C_h b u t w a)).2.2.1 =
      (O q.castSucc w).2.2.1 := by cases b <;> rfl
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  rw [he]
  simp only [preClearFlag, renewalFlag, hn, withAuxiliary_source]

/-- The actual sampler atom is zero on absence and its literal fibre mass
on a present invocation. It reads only the physical PRE-call source. -/
def callAtom (A : Outcome p) (z : Source p) : ℝ :=
  match ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z with
  | none => 0
  | some c => (AssignmentParameterFibreKernel.fibreMass p c.2 A).toReal

/-- Real weighted retained-endpoint atoms against every bounded Borel
physical-past test, under each original fibre-weighted branch lift. -/
theorem retainedEndpoint_weighted_atom (htq : t.val < q.val) (A : Outcome p)
    (Phi : Source p → ℝ) (hPhi : Measurable Phi) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ z, ‖Phi z‖ ≤ B) :
    (∫ w : Lift, if w ∈ retainedNextEvent rate rewards C_star C_h control0 b u t q then
      if retainedEndpoint rate (t := t) q (O q.castSucc w) = A then
        Phi (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (O q.castSucc w).1.1.1.2)
      else 0 else 0 ∂Lambda) =
    ∫ w : Lift, if w ∈ retainedNextEvent rate rewards C_star C_h control0 b u t q then
      Phi (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (O q.castSucc w).1.1.1.2) *
        callAtom rate rewards C_star C_h q A (O q.castSucc w).1.1.1.2 else 0 ∂Lambda := by
  let E := retainedNextEvent rate rewards C_star C_h control0 b u t q
  let past := fun w : Lift => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val
    (O q.castSucc w).1.1.1.2
  let f := fun w : Lift => if w ∈ E then
    if retainedEndpoint rate (t := t) q (O q.castSucc w) = A then Phi (past w) else 0 else 0
  have hp : Measurable past :=
    (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 q.val).comp
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
  have he := measurableSet_retainedNextEvent rate rewards C_star C_h control0 b u t q
  have hendpoint := (measurable_retainedEndpoint rate (t := t) q).comp
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)
  have hf : Measurable f := Measurable.ite he
    (Measurable.ite (measurableSet_eq_fun hendpoint measurable_const) (hPhi.comp hp) measurable_const)
    measurable_const
  have hb (w) : ‖f w‖ ≤ B := by
    dsimp only [f]
    split_ifs <;> first | exact hB _ | simpa only [norm_zero] using hB0
  rw [← refreshAgain_integral rate rewards C_star C_h control0 b u t f hf B hb]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change (∫ a, f (refreshAgain rate rewards C_star C_h b u t w a) ∂refreshAuxiliaryLaw b t) =
    if w ∈ E then Phi (past w) * callAtom rate rewards C_star C_h q A (O q.castSucc w).1.1.1.2 else 0
  have hs (a : RefreshAuxiliary b t) :
      (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)).1.1.1.2 =
      (O q.castSucc w).1.1.1.2 := withAuxiliary_source rate rewards C_star C_h control0 b u t q.castSucc w _
  have hE (a : RefreshAuxiliary b t) : refreshAgain rate rewards C_star C_h b u t w a ∈ E ↔ w ∈ E :=
    withAuxiliary_retainedNextEvent_iff rate rewards C_star C_h control0 b u t q w _
  by_cases hw : w ∈ E
  · obtain ⟨cutoff, theta, hc, _hnone, hatom⟩ :=
      actual_nextNonrenewed_refresh_atoms rate rewards C_star C_h control0 b u t q htq w hw.1 hw.2.1 hw.2.2
    have hm : Measurable (fun a : RefreshAuxiliary b t =>
        retainedEndpoint rate (t := t) q (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a))) :=
      hendpoint.comp ((measurable_refreshAgain rate rewards C_star C_h b u t).comp
        ((measurable_const (a := w)).prodMk measurable_id))
    have hset := hm (measurableSet_singleton A)
    calc
      _ = ∫ a : RefreshAuxiliary b t, if retainedEndpoint rate (t := t) q
          (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)) = A then Phi (past w) else 0
          ∂refreshAuxiliaryLaw b t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => by simp only [f, (hE a).mpr hw, ite_true, past, hs a]
      _ = _ := by
        rw [ite_eq_left hw]
        have hS : MeasurableSet {a : RefreshAuxiliary b t | retainedEndpoint rate (t := t) q
            (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)) = A} := by
          simpa only [Set.preimage_singleton] using hset
        have hid : (fun a : RefreshAuxiliary b t => if retainedEndpoint rate (t := t) q
            (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)) = A then Phi (past w) else 0) =
            {a | retainedEndpoint rate (t := t) q
              (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)) = A}.indicator
              (fun _ => Phi (past w)) := by
          funext a
          by_cases h : retainedEndpoint rate (t := t) q
              (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)) = A
            <;> simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true, ite_false]
        have hmass : refreshAuxiliaryLaw b t {a | retainedEndpoint rate (t := t) q
            (O q.castSucc (refreshAgain rate rewards C_star C_h b u t w a)) = A} =
            AssignmentParameterFibreKernel.fibreMass p theta A := hatom (refreshSplit b t w.1.2).1 A
        rw [hid, integral_indicator_const (Phi (past w)) hS, smul_eq_mul, measureReal_def, hmass]
        simp only [callAtom, hc]
        exact mul_comm _ _
  · have hz : ∀ a, f (refreshAgain rate rewards C_star C_h b u t w a) = 0 :=
      fun a => by simp only [f, (hE a).not.mpr hw, ite_false]
    simp only [hz, integral_zero, ite_eq_right hw]

/-- Corrected calls keep the generated endpoint. Renewed calls consume
label one of the fresh pair; label zero remains available for the update. -/
def installationEndpoint (i : NextInput rate t q × AssignmentParameterFibreKernel.Theta p) : Outcome p :=
  endpointChoice (renewalFlag rate rewards C_star C_h (t := t) q i.1.1,
    ((i.2, i.1.2.2), retainedEndpoint rate (t := t) q i.1.1))

theorem measurable_installationEndpoint :
    Measurable (installationEndpoint rate rewards C_star C_h (t := t) q) := by
  exact (measurable_endpointChoice (p := p)).comp
    (((measurable_renewalFlag rate rewards C_star C_h (t := t) q).comp measurable_fst.fst).prodMk
      ((measurable_snd.prodMk measurable_fst.snd.snd).prodMk
        ((measurable_retainedEndpoint rate (t := t) q).comp measurable_fst.fst)))

/-- The optional fibre parameter uses the actual call selector. Absent calls
and analytically stopped inputs have no replacement instruction. -/
def installationSelection (i : NextInput rate t q) :
    Option (AssignmentParameterFibreKernel.Theta p × Outcome p) :=
  match ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q i.1.1.1.1.2 with
  | none => none
  | some c => if preClearFlag rate (t := t) q i.1 then
      some (c.2, installationEndpoint rate rewards C_star C_h (t := t) q (i, c.2)) else none

theorem measurable_installationSelection (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (installationSelection rate rewards C_star C_h (t := t) q) := by
  unfold installationSelection
  have hc : Measurable (fun i : NextInput rate t q =>
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q i.1.1.1.1.2) :=
    ((ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 q).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (q.val + 1)) le_rfl).comp
        measurable_fst.fst.fst.fst.snd
  have he : Measurable (fun v : NextInput rate t q × (Fin p.T × AssignmentParameterFibreKernel.Theta p) =>
      some (v.2.2, installationEndpoint rate rewards C_star C_h (t := t) q (v.1, v.2.2))) :=
    LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_snd.snd.prodMk
        ((measurable_installationEndpoint rate rewards C_star C_h (t := t) q).comp
          (measurable_fst.prodMk measurable_snd.snd)))
  have hs : Measurable (fun v : NextInput rate t q × (Fin p.T × AssignmentParameterFibreKernel.Theta p) =>
      if preClearFlag rate (t := t) q v.1.1 then
        some (v.2.2, installationEndpoint rate rewards C_star C_h (t := t) q (v.1, v.2.2))
      else none) :=
    Measurable.ite (measurableSet_eq_fun
      ((measurable_preClearFlag rate (t := t) q).comp measurable_fst.fst) measurable_const) he measurable_const
  convert measurable_option_cases _ hc (fun _ => none) measurable_const _ hs using 1
  funext i
  cases ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q i.1.1.1.1.2 <;> rfl

/-- The existing complete current vector, for the literal no-replacement
branches. It retains orientation and all unread coordinates. -/
def currentVector (i : NextInput rate t q) : Vector p :=
  ReferenceFirstCollectionRenewalVectorInsertion.av q i.1.1.1.1.2

theorem measurable_currentVector : Measurable (currentVector rate (t := t) q) :=
  (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
    (((ReferenceSourceCurrentControlFreshness.measurable_u_t q).fst).comp
      measurable_fst.fst.fst.fst.snd)

/-- Full assignment-fibre insertion using the literal call and branch flags.
The inherited null-fibre convention retains all zero atoms. -/
def nextVectorKernel (control0 : ContinuousLearningRows.TimeControl p) : ProbabilityTheory.Kernel (NextInput rate t q) (Vector p) where
  toFun i := match installationSelection rate rewards C_star C_h (t := t) q i with
    | none => Measure.dirac (currentVector rate (t := t) q i)
    | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2
  measurable' := by
    convert measurable_option_cases (X := NextInput rate t q)
      (A := AssignmentParameterFibreKernel.Theta p × Outcome p) (B := Measure (Vector p)) _
      (measurable_installationSelection rate rewards C_star C_h (t := t) (q := q) control0)
      (fun i => Measure.dirac (currentVector rate (t := t) q i))
      (Measure.measurable_dirac.comp (measurable_currentVector rate (t := t) q))
      (fun v => AssignmentParameterFibreKernel.fibreMeasure p v.2.1 v.2.2)
      ((AssignmentParameterFibreKernel.assignmentParameterFibreKernel p).measurable.comp measurable_snd) using 1
    funext i
    cases installationSelection rate rewards C_star C_h (t := t) q i <;> rfl

theorem nextVectorKernel_apply (i : NextInput rate t q) :
    nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 i =
      match installationSelection rate rewards C_star C_h (t := t) q i with
      | none => Measure.dirac (currentVector rate (t := t) q i)
      | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2 := rfl

instance nextVectorKernel_markov : ProbabilityTheory.IsMarkovKernel
    (nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0) where
  isProbabilityMeasure i := by
    change IsProbabilityMeasure (match installationSelection rate rewards C_star C_h (t := t) q i with
      | none => Measure.dirac (currentVector rate (t := t) q i)
      | some a => AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2)
    cases installationSelection rate rewards C_star C_h (t := t) q i with
    | none => exact Measure.dirac.isProbabilityMeasure
    | some a => exact FiniteFibreLift.instIsProbabilityMeasureFibreMeasure _ _ _

/-- The literal original lift supplies its own generated observation and
current auxiliary pair. The entire old lift is retained on this extension. -/
def actualNextInput (w : Lift) : NextInput rate t q :=
  (O q.castSucc w, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.auxiliaryPair q w.1.2)

theorem measurable_actualNextInput : Measurable (actualNextInput rate rewards C_star C_h control0 b u t q) :=
  (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).prodMk
    ((ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_auxiliaryPair q).comp measurable_fst.snd)

/-- On a stopped PRE state the physical source follows its original draw. -/
theorem nextVectorKernel_of_preStopped (i : NextInput rate t q)
    (hi : preClearFlag rate (t := t) q i.1 = false) :
    nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 i =
      Measure.dirac (currentVector rate (t := t) q i) := by
  rw [nextVectorKernel_apply]
  unfold installationSelection
  cases ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q i.1.1.1.1.2 <;>
    simp only [hi, Bool.false_eq_true, ite_eq_right, not_false_eq_true]

theorem nextVectorKernel_of_call (i : NextInput rate t q)
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q i.1.1.1.1.2 =
      some (cutoff, theta)) (hi : preClearFlag rate (t := t) q i.1 = true) :
    nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 i =
      AssignmentParameterFibreKernel.fibreMeasure p theta
        (installationEndpoint rate rewards C_star C_h (t := t) q (i, theta)) := by
  rw [nextVectorKernel_apply]
  simp only [installationSelection, hc, hi, ite_true]

/-- Exact joint endpoint/full-vector fibre identity on every retained section.
The right side keeps all K+1 coordinates and includes none and null fibres. -/
theorem retainedEndpoint_vector_fibre (htq : t.val < q.val) (w : Lift)
    (hw : w ∈ retainedNextEvent rate rewards C_star C_h control0 b u t q) :
    ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p),
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
        (O q.castSucc w).1.1.1.2 = some (cutoff, theta) ∧
      ∀ (old : OldAuxiliary b t) (A : Outcome p) (C : Set (Vector p)), MeasurableSet C →
        (∫⁻ a, if retainedEndpoint rate (t := t) q
            (O q.castSucc (withAuxiliary rate rewards C_star C_h b u t w ((refreshSplit b t).symm (old, a)))) = A then
          nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0
            (actualNextInput rate rewards C_star C_h control0 b u t q
              (withAuxiliary rate rewards C_star C_h b u t w ((refreshSplit b t).symm (old, a)))) C
          else 0 ∂refreshAuxiliaryLaw b t) =
          ContinuousControlSlice.assignmentLaw p.K
            (C ∩ {v | AssignmentParameterFibreKernel.successfulSlowSet p theta v = A}) := by
  obtain ⟨cutoff, theta, hc, _hnone, hatom⟩ :=
    actual_nextNonrenewed_refresh_atoms rate rewards C_star C_h control0 b u t q htq w hw.1 hw.2.1 hw.2.2
  refine ⟨cutoff, theta, hc, ?_⟩
  intro old A C hC
  let wa := fun a : RefreshAuxiliary b t =>
    withAuxiliary rate rewards C_star C_h b u t w ((refreshSplit b t).symm (old, a))
  let endpoint := fun a => retainedEndpoint rate (t := t) q (O q.castSucc (wa a))
  have hwa : Measurable wa :=
    (measurable_const.prodMk ((refreshSplit b t).symm.measurable.comp
      ((measurable_const (a := old)).prodMk measurable_id))).prodMk measurable_const
  have hset := ((measurable_retainedEndpoint rate (t := t) q).comp
    ((measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp hwa))
      (measurableSet_singleton A)
  have hk (a) : nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0
      (actualNextInput rate rewards C_star C_h control0 b u t q (wa a)) =
      AssignmentParameterFibreKernel.fibreMeasure p theta (endpoint a) := by
    have hs : (O q.castSucc (wa a)).1.1.1.2 = (O q.castSucc w).1.1.1.2 :=
      withAuxiliary_source rate rewards C_star C_h control0 b u t q.castSucc w _
    have hn : (O q.castSucc (wa a)).2.2.1 = (O q.castSucc w).2.2.1 := by cases b <;> rfl
    have hclear : preClearFlag rate (t := t) q (O q.castSucc (wa a)) = true := by
      simpa only [preClearFlag, hn] using hw.2.1
    have hnr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc (wa a)) = false := by
      simpa only [renewalFlag, hs] using hw.2.2
    rw [nextVectorKernel_of_call rate rewards C_star C_h (t := t) (q := q) control0 _ cutoff theta
      (by exact hs ▸ hc) hclear]
    simp only [installationEndpoint, endpointChoice, actualNextInput, hnr]
    rfl
  have htest : (fun a => if endpoint a = A then nextVectorKernel rate rewards C_star C_h
      (t := t) (q := q) control0 (actualNextInput rate rewards C_star C_h control0 b u t q (wa a)) C else 0) =
      {a | endpoint a = A}.indicator (fun _ => AssignmentParameterFibreKernel.fibreMeasure p theta A C) := by
    funext a
    by_cases h : endpoint a = A <;> simp only [Set.indicator, Set.mem_ofPred_eq, hk, h, ite_true, ite_false]
  have hS : MeasurableSet {a | endpoint a = A} := by
    simpa only [Set.preimage_singleton, endpoint, Function.comp_def] using hset
  have hmass : refreshAuxiliaryLaw b t {a | endpoint a = A} =
      AssignmentParameterFibreKernel.fibreMass p theta A := hatom old A
  rw [htest, lintegral_indicator_const hS, hmass, mul_comm]
  have hcancel := congrArg (fun mu : Measure (Vector p) => mu C)
    (AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure p theta A)
  simpa only [Measure.smul_apply, Measure.restrict_apply hC, smul_eq_mul, FiniteFibreLift.fibre, Set.preimage_singleton] using hcancel

/-- Averaging the actual corrected insertion kernel gives the whole cube
on each fixed original-source/first-vector/old-array section. This section
identity makes no assertion about the global newly inserted-source marginal. -/
theorem retainedNext_vector_marginal (htq : t.val < q.val) (w : Lift)
    (hw : w ∈ retainedNextEvent rate rewards C_star C_h control0 b u t q)
    (old : OldAuxiliary b t) (C : Set (Vector p)) (hC : MeasurableSet C) :
    (∫⁻ a, nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0
      (actualNextInput rate rewards C_star C_h control0 b u t q
        (withAuxiliary rate rewards C_star C_h b u t w ((refreshSplit b t).symm (old, a)))) C
      ∂refreshAuxiliaryLaw b t) = ContinuousControlSlice.assignmentLaw p.K C := by
  obtain ⟨cutoff, theta, _hc, hfibre⟩ :=
    retainedEndpoint_vector_fibre rate rewards C_star C_h control0 b u t q htq w hw
  let wa := fun a : RefreshAuxiliary b t =>
    withAuxiliary rate rewards C_star C_h b u t w ((refreshSplit b t).symm (old, a))
  have hwa : Measurable wa :=
    (measurable_const.prodMk ((refreshSplit b t).symm.measurable.comp
      ((measurable_const (a := old)).prodMk measurable_id))).prodMk measurable_const
  have he := (measurable_retainedEndpoint rate (t := t) q).comp
    ((measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp hwa)
  have hk := (ProbabilityTheory.Kernel.measurable_coe
    (nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0) hC).comp
      ((measurable_actualNextInput rate rewards C_star C_h control0 b u t q).comp hwa)
  have hs := lintegral_finsetSum (μ := refreshAuxiliaryLaw b t) Finset.univ
    (f := fun A a => if retainedEndpoint rate (t := t) q (O q.castSucc (wa a)) = A then
      nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0
        (actualNextInput rate rewards C_star C_h control0 b u t q (wa a)) C else 0)
    (fun A _ => Measurable.ite (measurableSet_eq_fun he (measurable_const (a := A))) hk measurable_const)
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hs
  rw [hs]
  simp_rw [wa, hfibre old _ C hC]
  have h := congrArg (fun mu : Measure (Vector p) => mu C)
    (FiniteFibreLift.sum_restrict_fibre (ContinuousControlSlice.assignmentLaw p.K)
      (AssignmentParameterFibreKernel.successfulSlowSet p theta)
      ((AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
        (measurable_const.prodMk measurable_id)))
  simpa only [Measure.finsetSum_apply, Measure.restrict_apply hC, FiniteFibreLift.fibre,
    Set.preimage_singleton] using h

end InstallationKernel

end Bandits.Support.ReferenceNextRetainedEndpointFibreLaw
