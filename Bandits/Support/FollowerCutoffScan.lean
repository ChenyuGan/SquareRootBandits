/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalEpisodePolicy
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ReplayWeightStability
public import Mathlib.Data.Finset.Sort

/-!
# Literal physical follower cutoffs and chronological proposal scan

The physical calendar formulas are from
`sources/zip4/manuscript/06_interruptions.tex:9-14,197-203,270-275`.
The horizon is the source horizon in
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-104`; its strict
positivity is derived from the actual learning-rate cap using the accepted
`CanonicalEpisodePolicy.horizon_pos`. Proposal coordinates are the `prop`
scalars of an actual complete row, as specified by
`sources/zip4/manuscript/appendix_b_communication.tex:25-44`. The strict
threshold convention agrees with
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-77`.

Here `Fin T` stores zero-based table coordinates. Its value `i.val` is the
proposal coordinate for one-based calendar round `i.val + 1`, matching the
source's `B_s` at offset `s - 1`. A scan reads past coordinates in increasing
calendar order and short-circuits at the first true bit or at the clipped grid
boundary. The logical episode clock remains the distinct
`CanonicalEpisodePolicy` interface. No execution scheduler, freshness law, or
follower-state transition is defined here.
-/

@[expose] public section

namespace Bandits.Support.FollowerCutoffScan

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReplayWeightStability

/-- The source one-based calendar round represented by a table coordinate. -/
def calendarRound {T : ℕ} (i : Fin T) : ℕ := i.val + 1

/-- The actual physical grid endpoint `g(σ)`, clipped at `T + 1`.  The input
coordinate `sigma` represents source round `sigma.val + 1`. -/
noncomputable def gridBoundary (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma : Fin p.T) : ℕ :=
  min (p.T + 1)
    (ReplayWeightStability.episodeHorizon eta *
      ((sigma.val + 1) / ReplayWeightStability.episodeHorizon eta + 1))

/-- The public proposal coordinates whose one-based source rounds lie in
`[sigma,T)`.  The last physical table coordinate is excluded because it is
`B_T`, while the source cutoff minimum ranges only over `s < T`. -/
def proposalCoordinates (p : ConstructorDimensions.Parameters)
    (sigma : Fin p.T) : Finset (Fin p.T) :=
  Finset.univ.filter fun i => sigma.val ≤ i.val ∧ i.val + 1 < p.T

/-- Past proposal coordinates, with the current decision coordinate excluded.
The source interval `[sigma,t)` corresponds to indices `sigma.val ≤ i.val <
t.val`. -/
def pastProposalCoordinates (p : ConstructorDimensions.Parameters)
    (sigma t : Fin p.T) : Finset (Fin p.T) :=
  (proposalCoordinates p sigma).filter fun i => i.val < t.val

/-- The cutoff endpoint contributed by a true proposal at coordinate `i`. -/
def proposalEndpoint {T : ℕ} (i : Fin T) : ℕ := i.val + 2

/-- The finite set of endpoints contributed by true proposal bits on a finite
coordinate carrier. -/
def trueProposalEndpoints {T : ℕ} (bits : Fin T → Bool)
    (coordinates : Finset (Fin T)) : Finset ℕ :=
  ((coordinates.filter fun i => bits i = true).image proposalEndpoint)

/-- The explicit finite carrier for the source's first physical cutoff
`min({g} ∪ {s+1 : sigma ≤ s < T, B_s})`. -/
noncomputable def firstCutoffCarrier (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma : Fin p.T) (bits : Fin p.T → Bool) : Finset ℕ :=
  insert (gridBoundary p eta sigma)
    (trueProposalEndpoints bits (proposalCoordinates p sigma))

theorem firstCutoffCarrier_nonempty (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma : Fin p.T) (bits : Fin p.T → Bool) :
    (firstCutoffCarrier p eta sigma bits).Nonempty := by
  exact ⟨gridBoundary p eta sigma, Finset.mem_insert_self _ _⟩

/-- The actual first cutoff `u` from the source, as a minimum over its explicit
nonempty finite carrier. -/
noncomputable def firstCutoff (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma : Fin p.T) (bits : Fin p.T → Bool) : ℕ :=
  (firstCutoffCarrier p eta sigma bits).min'
    (firstCutoffCarrier_nonempty p eta sigma bits)

/-- The explicit finite carrier for the follower's known endpoint `ell`,
including both mandatory endpoints `t+1` and `g`. -/
noncomputable def knownCutoffCarrier (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (bits : Fin p.T → Bool) : Finset ℕ :=
  insert (t.val + 2)
    (insert (gridBoundary p eta sigma)
      (trueProposalEndpoints bits (pastProposalCoordinates p sigma t)))

theorem knownCutoffCarrier_nonempty (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (bits : Fin p.T → Bool) :
    (knownCutoffCarrier p eta sigma t bits).Nonempty := by
  exact ⟨t.val + 2, Finset.mem_insert_self _ _⟩

/-- The literal known endpoint `ell` from the source's finite minimum. -/
noncomputable def knownCutoff (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (bits : Fin p.T → Bool) : ℕ :=
  (knownCutoffCarrier p eta sigma t bits).min'
    (knownCutoffCarrier_nonempty p eta sigma t bits)

/-- The exact source proposal hazard `h = 4*m*eta`. -/
def proposalHazard (p : ConstructorDimensions.Parameters) (eta : ℝ) : ℝ :=
  4 * (p.m : ℝ) * eta

/-- Apply the accepted strict continuous-threshold convention to one literal
`[0,1)` scalar. -/
noncomputable def thresholdProposalBit (v : ContinuousControlSlice.Scalar)
    (hazard : ℝ) : Bool := decide (v.val < hazard)

/-- Read exactly the `prop` scalar in one actual complete row and apply the
source proposal hazard. The row is a single selected `CompleteRow`; there is no
family index or alternate label in this interface. -/
noncomputable def completeRowProposalBit (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (row : CompletePublicTable.CompleteRow p) (i : Fin p.T) : Bool :=
  thresholdProposalBit
    ((CompletePublicTable.completeRowLearning p row i).1
      (ContinuousControlSlice.Label.prop))
    (proposalHazard p eta)

/-- The selected complete-row proposal bit is its `prop` scalar's strict
comparison with `4*m*eta`, with no other row coordinate involved. -/
theorem completeRowProposalBit_eq (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (row : CompletePublicTable.CompleteRow p) (i : Fin p.T) :
    completeRowProposalBit p eta row i =
      decide (((CompletePublicTable.completeRowLearning p row i).1
        (ContinuousControlSlice.Label.prop)).val < 4 * (p.m : ℝ) * eta) := by
  rfl

/-- The result of the chronological early-stop scan. `inspected` contains
zero-based table coordinates, corresponding to the one-based calendar rounds
obtained through `calendarRound`. -/
structure ScanResult (T : ℕ) where
  endpoint : ℕ
  inspected : List (Fin T)
  deriving DecidableEq

/-- Scan an already ordered list of past proposal coordinates. The endpoint
`base` is the earlier of the current decision's `t+1` and the clipped grid
boundary. A true proposal returns immediately; a coordinate at or beyond the
grid boundary returns without reading it. -/
def chronologicalScanLoop {T : ℕ} (bits : Fin T → Bool)
    (base grid : ℕ) : List (Fin T) → ScanResult T
  | [] => ⟨base, []⟩
  | i :: rest =>
      if i.val + 1 < grid then
        if bits i = true then ⟨proposalEndpoint i, [i]⟩
        else
          let tail := chronologicalScanLoop bits base grid rest
          ⟨tail.endpoint, i :: tail.inspected⟩
      else ⟨base, []⟩

theorem chronologicalScanLoop_cons_true {T : ℕ} (bits : Fin T → Bool)
    (base grid : ℕ) (i : Fin T) (rest : List (Fin T))
    (hgrid : i.val + 1 < grid) (hbit : bits i = true) :
    chronologicalScanLoop bits base grid (i :: rest) =
      ⟨proposalEndpoint i, [i]⟩ := by
  change (if i.val + 1 < grid then
      if bits i = true then ScanResult.mk (proposalEndpoint i) [i]
      else ScanResult.mk (chronologicalScanLoop bits base grid rest).endpoint
        (i :: (chronologicalScanLoop bits base grid rest).inspected)
    else ScanResult.mk base []) = _
  simp [hgrid, hbit]

theorem chronologicalScanLoop_cons_false {T : ℕ} (bits : Fin T → Bool)
    (base grid : ℕ) (i : Fin T) (rest : List (Fin T))
    (hgrid : i.val + 1 < grid) (hbit : bits i ≠ true) :
    chronologicalScanLoop bits base grid (i :: rest) =
      ⟨(chronologicalScanLoop bits base grid rest).endpoint,
        i :: (chronologicalScanLoop bits base grid rest).inspected⟩ := by
  change (if i.val + 1 < grid then
      if bits i = true then ScanResult.mk (proposalEndpoint i) [i]
      else ScanResult.mk (chronologicalScanLoop bits base grid rest).endpoint
        (i :: (chronologicalScanLoop bits base grid rest).inspected)
    else ScanResult.mk base []) = _
  simp [hgrid, hbit]

theorem chronologicalScanLoop_cons_grid {T : ℕ} (bits : Fin T → Bool)
    (base grid : ℕ) (i : Fin T) (rest : List (Fin T))
    (hgrid : ¬ i.val + 1 < grid) :
    chronologicalScanLoop bits base grid (i :: rest) = ⟨base, []⟩ := by
  change (if i.val + 1 < grid then
      if bits i = true then ScanResult.mk (proposalEndpoint i) [i]
      else ScanResult.mk (chronologicalScanLoop bits base grid rest).endpoint
        (i :: (chronologicalScanLoop bits base grid rest).inspected)
    else ScanResult.mk base []) = _
  simp [hgrid]

/-- The actual follower scan on precisely the public proposal coordinates from
`[sigma,t)`, ordered chronologically. -/
noncomputable def followerCutoffScan (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (_hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    ScanResult p.T :=
  chronologicalScanLoop bits (min (t.val + 2) (gridBoundary p eta sigma))
    (gridBoundary p eta sigma)
    ((pastProposalCoordinates p sigma t).sort (· ≤ ·))

/-- The finite carrier whose minimum is the result of scanning a list: its
mandatory values are the explicit decision and grid endpoints, and its other
values are exactly the true proposals in the list. -/
def scanEndpointCarrier {T : ℕ} (bits : Fin T → Bool)
    (decisionEndpoint grid : ℕ) (coordinates : List (Fin T)) : Finset ℕ :=
  insert decisionEndpoint
    (insert grid (trueProposalEndpoints bits coordinates.toFinset))

theorem scanEndpointCarrier_nonempty {T : ℕ} (bits : Fin T → Bool)
    (decisionEndpoint grid : ℕ) (coordinates : List (Fin T)) :
    (scanEndpointCarrier bits decisionEndpoint grid coordinates).Nonempty := by
  exact ⟨decisionEndpoint, Finset.mem_insert_self _ _⟩

/-- Minimum characterization of the operational scan loop. Its proof is a
chronological induction: later true events cannot precede an earlier true
event, and every event at or beyond `grid` is later than the grid endpoint. -/
theorem chronologicalScanLoop_endpoint_eq_min {T : ℕ}
    (bits : Fin T → Bool) (decisionEndpoint grid : ℕ)
    (coordinates : List (Fin T))
    (hordered : coordinates.Pairwise fun i j => i.val < j.val)
    (hbefore : ∀ i ∈ coordinates, i.val + 1 < decisionEndpoint) :
    (chronologicalScanLoop bits (min decisionEndpoint grid) grid coordinates).endpoint =
      (scanEndpointCarrier bits decisionEndpoint grid coordinates).min'
        (scanEndpointCarrier_nonempty bits decisionEndpoint grid coordinates) := by
  induction coordinates with
  | nil =>
      simp [chronologicalScanLoop, scanEndpointCarrier, trueProposalEndpoints]
  | cons i rest ih =>
      have hhead : i.val + 1 < decisionEndpoint := hbefore i (by simp)
      have htailBefore : ∀ j ∈ rest, j.val + 1 < decisionEndpoint := by
        intro j hj
        exact hbefore j (by simp [hj])
      rcases List.pairwise_cons.mp hordered with ⟨hiRest, hrestOrdered⟩
      by_cases hgrid : i.val + 1 < grid
      · by_cases hbit : bits i = true
        · have hmin :
              (scanEndpointCarrier bits decisionEndpoint grid (i :: rest)).min'
                (scanEndpointCarrier_nonempty bits decisionEndpoint grid (i :: rest)) =
                proposalEndpoint i := by
            apply (Finset.min'_eq_iff _ _ (proposalEndpoint i)).2
            constructor
            · apply Finset.mem_insert_of_mem
              apply Finset.mem_insert_of_mem
              unfold trueProposalEndpoints
              apply Finset.mem_image.mpr
              exact ⟨i, Finset.mem_filter.mpr ⟨by simp, hbit⟩, rfl⟩
            · intro y hy
              simp only [scanEndpointCarrier, Finset.mem_insert] at hy
              rcases hy with hdec | hy
              · rw [hdec]
                simp only [proposalEndpoint]
                omega
              · rcases hy with hgridValue | hevent
                · rw [hgridValue]
                  simp only [proposalEndpoint]
                  omega
                · obtain ⟨j, hj, hy⟩ := Finset.mem_image.mp hevent
                  have hj' := Finset.mem_filter.mp hj
                  have hjmem : j ∈ i :: rest := by
                    simpa only [List.mem_toFinset] using hj'.1
                  rcases List.mem_cons.mp hjmem with hji | hjrest
                  · subst j
                    exact le_of_eq hy
                  · have hij := hiRest j hjrest
                    simp only [proposalEndpoint] at hy ⊢
                    omega
          rw [chronologicalScanLoop_cons_true bits (min decisionEndpoint grid) grid
            i rest hgrid hbit]
          exact hmin.symm
        · have hevents :
              trueProposalEndpoints bits (i :: rest).toFinset =
                trueProposalEndpoints bits rest.toFinset := by
            unfold trueProposalEndpoints
            ext y
            simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset,
              List.mem_cons]
            constructor
            · rintro ⟨a, ⟨ha, htrue⟩, hval⟩
              rcases ha with rfl | ha
              · exact False.elim (hbit htrue)
              · exact ⟨a, ⟨ha, htrue⟩, hval⟩
            · rintro ⟨a, ⟨ha, htrue⟩, hval⟩
              exact ⟨a, ⟨Or.inr ha, htrue⟩, hval⟩
          have hcarrier :
              scanEndpointCarrier bits decisionEndpoint grid (i :: rest) =
                scanEndpointCarrier bits decisionEndpoint grid rest := by
            simp only [scanEndpointCarrier, hevents]
          rw [chronologicalScanLoop_cons_false bits (min decisionEndpoint grid) grid
            i rest hgrid hbit]
          have hminEq :
              (scanEndpointCarrier bits decisionEndpoint grid rest).min'
                  (scanEndpointCarrier_nonempty bits decisionEndpoint grid rest) =
                (scanEndpointCarrier bits decisionEndpoint grid (i :: rest)).min'
                  (scanEndpointCarrier_nonempty bits decisionEndpoint grid (i :: rest)) := by
            apply le_antisymm
            · apply Finset.min'_le
              rw [← hcarrier]
              exact Finset.min'_mem _ _
            · apply Finset.min'_le
              rw [hcarrier]
              exact Finset.min'_mem _ _
          calc
            (chronologicalScanLoop bits (min decisionEndpoint grid) grid rest).endpoint =
                (scanEndpointCarrier bits decisionEndpoint grid rest).min'
                  (scanEndpointCarrier_nonempty bits decisionEndpoint grid rest) :=
              ih hrestOrdered htailBefore
            _ = (scanEndpointCarrier bits decisionEndpoint grid (i :: rest)).min'
                  (scanEndpointCarrier_nonempty bits decisionEndpoint grid (i :: rest)) :=
              hminEq
      · have hgridLe : grid ≤ i.val + 1 := by omega
        have hgridStop : grid ≤ decisionEndpoint := by omega
        have hlarge : ∀ j ∈ i :: rest, grid ≤ j.val + 1 := by
          intro j hj
          rcases List.mem_cons.mp hj with hji | hjrest
          · subst j
            exact hgridLe
          · have hij := hiRest j hjrest
            omega
        have hmin :
            (scanEndpointCarrier bits decisionEndpoint grid (i :: rest)).min'
              (scanEndpointCarrier_nonempty bits decisionEndpoint grid (i :: rest)) = grid := by
          apply (Finset.min'_eq_iff _ _ grid).2
          constructor
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · intro y hy
            simp only [scanEndpointCarrier, Finset.mem_insert] at hy
            rcases hy with hdec | hy
            · rw [hdec]
              exact hgridStop
            · rcases hy with hgridValue | hevent
              · rw [hgridValue]
              · obtain ⟨j, hj, hy⟩ := Finset.mem_image.mp hevent
                have hj' := Finset.mem_filter.mp hj
                have hjmem : j ∈ i :: rest := by
                  simpa only [List.mem_toFinset] using hj'.1
                have hjlarge := hlarge j hjmem
                simp only [proposalEndpoint] at hy ⊢
                omega
        rw [chronologicalScanLoop_cons_grid bits (min decisionEndpoint grid) grid
          i rest hgrid]
        change min decisionEndpoint grid = _
        rw [Nat.min_eq_right hgridStop]
        exact hmin.symm

/-- The loop's inspected list is a prefix of its ordered candidate list. -/
theorem chronologicalScanLoop_inspected_prefix {T : ℕ} (bits : Fin T → Bool)
    (base grid : ℕ) (coordinates : List (Fin T)) :
    ∃ suffix, coordinates =
      (chronologicalScanLoop bits base grid coordinates).inspected ++ suffix := by
  induction coordinates with
  | nil => exact ⟨[], rfl⟩
  | cons i rest ih =>
      by_cases hgrid : i.val + 1 < grid
      · by_cases hbit : bits i = true
        · exact ⟨rest, by
            rw [chronologicalScanLoop_cons_true bits base grid i rest hgrid hbit]
            rfl⟩
        · obtain ⟨suffix, hsuffix⟩ := ih
          refine ⟨suffix, ?_⟩
          rw [chronologicalScanLoop_cons_false bits base grid i rest hgrid hbit]
          calc
            i :: rest = i ::
                (chronologicalScanLoop bits base grid rest).inspected ++ suffix :=
              congrArg (List.cons i) hsuffix
            _ = (i :: (chronologicalScanLoop bits base grid rest).inspected) ++ suffix := by
              simp
      · exact ⟨i :: rest, by
          rw [chronologicalScanLoop_cons_grid bits base grid i rest hgrid]
          rfl⟩

/-- Every inspected coordinate belongs to the candidate list. -/
theorem chronologicalScanLoop_inspected_subset {T : ℕ} (bits : Fin T → Bool)
    (base grid : ℕ) (coordinates : List (Fin T)) :
    ∀ i ∈ (chronologicalScanLoop bits base grid coordinates).inspected,
      i ∈ coordinates := by
  intro i hi
  obtain ⟨suffix, hsuffix⟩ :=
    chronologicalScanLoop_inspected_prefix bits base grid coordinates
  rw [hsuffix]
  exact List.mem_append.mpr (Or.inl hi)

/-- The inspected coordinates are strictly increasing, so there are no
duplicates. -/
theorem chronologicalScanLoop_inspected_pairwise {T : ℕ}
    (bits : Fin T → Bool) (base grid : ℕ) (coordinates : List (Fin T))
    (hordered : coordinates.Pairwise fun i j => i.val < j.val) :
    ((chronologicalScanLoop bits base grid coordinates).inspected).Pairwise
      (fun i j => i.val < j.val) := by
  induction coordinates with
  | nil => simp [chronologicalScanLoop]
  | cons i rest ih =>
      rcases List.pairwise_cons.mp hordered with ⟨hiRest, hrestOrdered⟩
      by_cases hgrid : i.val + 1 < grid
      · by_cases hbit : bits i = true
        · rw [chronologicalScanLoop_cons_true bits base grid i rest hgrid hbit]
          simp
        · have htail := ih hrestOrdered
          rw [chronologicalScanLoop_cons_false bits base grid i rest hgrid hbit]
          apply List.pairwise_cons.mpr
          constructor
          · intro j hj
            have hjmem := chronologicalScanLoop_inspected_subset
              bits base grid rest j hj
            exact hiRest j hjmem
          · exact htail
      · rw [chronologicalScanLoop_cons_grid bits base grid i rest hgrid]
        simp

/-- The scan never inspects a proposal at or after the grid endpoint. -/
theorem chronologicalScanLoop_inspected_before_grid {T : ℕ}
    (bits : Fin T → Bool) (base grid : ℕ) (coordinates : List (Fin T))
    (i : Fin T) (hi : i ∈ (chronologicalScanLoop bits base grid coordinates).inspected) :
    i.val + 1 < grid := by
  induction coordinates with
  | nil => simp [chronologicalScanLoop] at hi
  | cons j rest ih =>
      by_cases hgrid : j.val + 1 < grid
      · by_cases hbit : bits j = true
        · rw [chronologicalScanLoop_cons_true bits base grid j rest hgrid hbit] at hi
          simp only [List.mem_singleton] at hi
          subst i
          exact hgrid
        · rw [chronologicalScanLoop_cons_false bits base grid j rest hgrid hbit] at hi
          simp only [List.mem_cons] at hi
          rcases hi with hji | hiRest
          · subst i
            exact hgrid
          · exact ih hiRest
      · rw [chronologicalScanLoop_cons_grid bits base grid j rest hgrid] at hi
        simp only [List.not_mem_nil] at hi

/-- Every inspected coordinate is strictly before the endpoint returned by the
scan. -/
theorem chronologicalScanLoop_inspected_before_endpoint {T : ℕ}
    (bits : Fin T → Bool) (decisionEndpoint grid : ℕ)
    (coordinates : List (Fin T))
    (hordered : coordinates.Pairwise fun i j => i.val < j.val)
    (hbefore : ∀ i ∈ coordinates, i.val + 1 < decisionEndpoint)
    (i : Fin T)
    (hi : i ∈ (chronologicalScanLoop bits (min decisionEndpoint grid) grid
      coordinates).inspected) :
    i.val + 1 <
      (chronologicalScanLoop bits (min decisionEndpoint grid) grid coordinates).endpoint := by
  induction coordinates with
  | nil => simp [chronologicalScanLoop] at hi
  | cons j rest ih =>
      have hjBefore := hbefore j (by simp)
      have hrestBefore : ∀ k ∈ rest, k.val + 1 < decisionEndpoint := by
        intro k hk
        exact hbefore k (by simp [hk])
      rcases List.pairwise_cons.mp hordered with ⟨hjRest, hrestOrdered⟩
      by_cases hgrid : j.val + 1 < grid
      · by_cases hbit : bits j = true
        · rw [chronologicalScanLoop_cons_true bits (min decisionEndpoint grid)
            grid j rest hgrid hbit] at hi ⊢
          simp only [List.mem_singleton] at hi
          subst i
          simp only [proposalEndpoint]
          omega
        · rw [chronologicalScanLoop_cons_false bits (min decisionEndpoint grid)
            grid j rest hgrid hbit] at hi ⊢
          simp only [List.mem_cons] at hi
          rcases hi with hji | hiRest
          · subst i
            have htailEq := chronologicalScanLoop_endpoint_eq_min bits
              decisionEndpoint grid rest hrestOrdered hrestBefore
            have htailMem :
                (chronologicalScanLoop bits (min decisionEndpoint grid) grid rest).endpoint ∈
                  scanEndpointCarrier bits decisionEndpoint grid rest := by
              rw [htailEq]
              exact Finset.min'_mem _ _
            simp only [scanEndpointCarrier, Finset.mem_insert] at htailMem
            rcases htailMem with hstop | htailMem
            · rw [hstop]
              exact hjBefore
            · rcases htailMem with hgridValue | hevent
              · rw [hgridValue]
                exact hgrid
              · obtain ⟨k, hk, hval⟩ := Finset.mem_image.mp hevent
                have hk' := Finset.mem_filter.mp hk
                have hkmem : k ∈ rest := by
                  simpa only [List.mem_toFinset] using hk'.1
                have hjk := hjRest k hkmem
                rw [← hval]
                simp only [proposalEndpoint]
                omega
          · exact ih hrestOrdered hrestBefore hiRest
      · rw [chronologicalScanLoop_cons_grid bits (min decisionEndpoint grid)
          grid j rest hgrid] at hi ⊢
        simp only [List.not_mem_nil] at hi

/-- Changing coordinates outside the scan's inspected list cannot change its
endpoint or its read list. This is a deterministic extensionality theorem; it
makes no probabilistic freshness claim. -/
theorem chronologicalScanLoop_noninterference {T : ℕ}
    (bits bits' : Fin T → Bool) (base grid : ℕ) (coordinates : List (Fin T))
    (hagree : ∀ i ∈ (chronologicalScanLoop bits base grid coordinates).inspected,
      bits i = bits' i) :
    chronologicalScanLoop bits base grid coordinates =
      chronologicalScanLoop bits' base grid coordinates := by
  induction coordinates with
  | nil => rfl
  | cons i rest ih =>
      by_cases hgrid : i.val + 1 < grid
      · by_cases hbit : bits i = true
        · have hiRead : i ∈
              (chronologicalScanLoop bits base grid (i :: rest)).inspected := by
            rw [chronologicalScanLoop_cons_true bits base grid i rest hgrid hbit]
            simp
          have hbitEq := hagree i hiRead
          have hbit' : bits' i = true := by
            rw [← hbitEq]
            exact hbit
          rw [chronologicalScanLoop_cons_true bits base grid i rest hgrid hbit,
            chronologicalScanLoop_cons_true bits' base grid i rest hgrid hbit']
        · have hiRead : i ∈
              (chronologicalScanLoop bits base grid (i :: rest)).inspected := by
            rw [chronologicalScanLoop_cons_false bits base grid i rest hgrid hbit]
            simp
          have hbitEq := hagree i hiRead
          have hbit' : bits' i ≠ true := by
            intro h'
            apply hbit
            rw [hbitEq, h']
          have htailAgree :
              ∀ j ∈ (chronologicalScanLoop bits base grid rest).inspected,
                bits j = bits' j := by
            intro j hj
            apply hagree j
            rw [chronologicalScanLoop_cons_false bits base grid i rest hgrid hbit]
            exact List.mem_cons_of_mem i hj
          have htailEq := ih htailAgree
          rw [chronologicalScanLoop_cons_false bits base grid i rest hgrid hbit,
            chronologicalScanLoop_cons_false bits' base grid i rest hgrid hbit']
          rw [htailEq]
      · rw [chronologicalScanLoop_cons_grid bits base grid i rest hgrid,
          chronologicalScanLoop_cons_grid bits' base grid i rest hgrid]

/-- The literal known endpoint is the minimum of the actual first cutoff and
the exclusive current-decision endpoint. Proposals at `s=t` can affect the
first cutoff when `t<T`, but are replaced by the `t+1` cap here. -/
theorem knownCutoff_eq_min_firstCutoff (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (sigma t : Fin p.T) (bits : Fin p.T → Bool) :
    knownCutoff p eta sigma t bits =
      min (firstCutoff p eta sigma bits) (t.val + 2) := by
  let u := firstCutoff p eta sigma bits
  let endpoint := t.val + 2
  let allEvents := trueProposalEndpoints bits (proposalCoordinates p sigma)
  let pastEvents := trueProposalEndpoints bits (pastProposalCoordinates p sigma t)
  let allCarrier := insert (gridBoundary p eta sigma) allEvents
  let pastCarrier := insert endpoint (insert (gridBoundary p eta sigma) pastEvents)
  have huMem : u ∈ allCarrier := by
    dsimp [u, allCarrier, firstCutoff]
    exact Finset.min'_mem _ _
  have huGrid : u ≤ gridBoundary p eta sigma := by
    dsimp [u, allCarrier, firstCutoff]
    exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hpastSubset : pastEvents ⊆ allEvents := by
    apply Finset.image_subset_iff.mpr
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiCoord, hbit⟩
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.filter_subset _ _ hiCoord, hbit⟩, rfl⟩
  by_cases huEnd : u ≤ endpoint
  · have huPastMem : u ∈ pastCarrier := by
      rcases Finset.mem_insert.mp huMem with huGridEq | huEvent
      · rw [huGridEq]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rcases Finset.mem_image.mp huEvent with ⟨i, hi, huEq⟩
        rcases Finset.mem_filter.mp hi with ⟨hiCoord, hbit⟩
        by_cases hiPast : i.val < t.val
        · have hiPastCoord : i ∈ pastProposalCoordinates p sigma t :=
            Finset.mem_filter.mpr ⟨hiCoord, hiPast⟩
          have hiPastBit : i ∈
              (pastProposalCoordinates p sigma t).filter fun j => bits j = true :=
            Finset.mem_filter.mpr ⟨hiPastCoord, hbit⟩
          have huPastEvent : u ∈ pastEvents := by
            rw [← huEq]
            exact Finset.mem_image.mpr ⟨i, hiPastBit, rfl⟩
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem huPastEvent)
        · have huEndpoint : u = endpoint := by
            dsimp [endpoint] at huEnd
            rw [← huEq] at huEnd
            rw [← huEq]
            simp only [proposalEndpoint] at huEnd ⊢
            have hiAfter : t.val ≤ i.val := by omega
            have huLe : i.val + 2 ≤ t.val + 2 := by omega
            omega
          rw [huEndpoint]
          exact Finset.mem_insert_self _ _
    have hcutoffLeU : knownCutoff p eta sigma t bits ≤ u := by
      dsimp [knownCutoff, pastCarrier]
      exact Finset.min'_le _ _ huPastMem
    have hUleCutoff : u ≤ knownCutoff p eta sigma t bits := by
      have hknownMem : knownCutoff p eta sigma t bits ∈ pastCarrier := by
        dsimp [knownCutoff, pastCarrier]
        exact Finset.min'_mem _ _
      rcases Finset.mem_insert.mp hknownMem with hEnd | hrest
      · rw [hEnd]
        exact huEnd
      · rcases Finset.mem_insert.mp hrest with hGrid | hEvent
        · rw [hGrid]
          exact huGrid
        · have hAll : knownCutoff p eta sigma t bits ∈ allCarrier :=
            Finset.mem_insert_of_mem (hpastSubset hEvent)
          dsimp [u, allCarrier, firstCutoff]
          exact Finset.min'_le _ _ hAll
    have hEq : knownCutoff p eta sigma t bits = u :=
      le_antisymm hcutoffLeU hUleCutoff
    rw [hEq]
    dsimp [u, endpoint]
    exact (Nat.min_eq_left huEnd).symm
  · have hendLt : endpoint < u := by omega
    have hminPast : knownCutoff p eta sigma t bits = endpoint := by
      apply (Finset.min'_eq_iff pastCarrier
        (knownCutoffCarrier_nonempty p eta sigma t bits) endpoint).2
      constructor
      · dsimp [pastCarrier]
        exact Finset.mem_insert_self _ _
      · intro y hy
        rcases Finset.mem_insert.mp hy with hyEnd | hyRest
        · rw [hyEnd]
        · rcases Finset.mem_insert.mp hyRest with hyGrid | hyEvent
          · rw [hyGrid]
            exact le_of_lt (lt_of_lt_of_le hendLt huGrid)
          · have hyAll : y ∈ allCarrier :=
              Finset.mem_insert_of_mem (hpastSubset hyEvent)
            have hule : u ≤ y := by
              dsimp [u, allCarrier, firstCutoff]
              exact Finset.min'_le _ _ hyAll
            exact le_of_lt (lt_of_lt_of_le hendLt hule)
    rw [hminPast]
    dsimp [u, endpoint]
    exact (Nat.min_eq_right (le_of_lt hendLt)).symm

/-- The literal finite endpoint formula agrees with the scan's endpoint. -/
theorem followerCutoffScan_endpoint_eq_knownCutoff
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    (followerCutoffScan p eta sigma t hσt bits).endpoint =
      knownCutoff p eta sigma t bits := by
  let coordinates := (pastProposalCoordinates p sigma t).sort (· ≤ ·)
  have hordered : coordinates.Pairwise fun i j => i.val < j.val := by
    dsimp [coordinates]
    simpa only [Fin.lt_def] using
      (Finset.sortedLT_sort (pastProposalCoordinates p sigma t)).pairwise
  have hbefore : ∀ i ∈ coordinates, i.val + 1 < t.val + 2 := by
    intro i hi
    have hi' : i ∈ pastProposalCoordinates p sigma t := by
      simpa only [coordinates, Finset.mem_sort] using hi
    simp only [pastProposalCoordinates, Finset.mem_filter, proposalCoordinates,
      Finset.mem_filter, Finset.mem_univ, true_and] at hi'
    omega
  have hspec := chronologicalScanLoop_endpoint_eq_min bits (t.val + 2)
    (gridBoundary p eta sigma) coordinates hordered hbefore
  have hcarrier : scanEndpointCarrier bits (t.val + 2) (gridBoundary p eta sigma)
      coordinates = knownCutoffCarrier p eta sigma t bits := by
    dsimp [scanEndpointCarrier, knownCutoffCarrier, coordinates,
      trueProposalEndpoints]
    simp only [Finset.sort_toFinset]
  change (chronologicalScanLoop bits (min (t.val + 2) (gridBoundary p eta sigma))
      (gridBoundary p eta sigma) coordinates).endpoint =
    (knownCutoffCarrier p eta sigma t bits).min'
      (knownCutoffCarrier_nonempty p eta sigma t bits)
  rw [hspec]
  apply le_antisymm
  · apply Finset.min'_le
    exact hcarrier.symm ▸ Finset.min'_mem _ _
  · apply Finset.min'_le
    exact hcarrier ▸ Finset.min'_mem _ _

/-- The scan and literal `ell` have the same endpoint. -/
theorem followerCutoffScan_endpoint_eq_min_firstCutoff
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    (followerCutoffScan p eta sigma t hσt bits).endpoint =
      min (firstCutoff p eta sigma bits) (t.val + 2) := by
  rw [followerCutoffScan_endpoint_eq_knownCutoff,
    knownCutoff_eq_min_firstCutoff]

/-- The actual grid horizon is positive, derived from eta positivity and the
manuscript's real learning-rate cap through the accepted logical-clock lemma. -/
theorem episodeHorizon_pos_of_source_cap
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : eta ≤ 1 /
      (1024 * (p.m : ℝ) * p.K * CanonicalRecordingRates.L_stab p)) :
    0 < ReplayWeightStability.episodeHorizon eta := by
  exact CanonicalEpisodePolicy.horizon_pos p eta heta hcap

/-- The clipped source grid endpoint is strictly after its one-based start and
never beyond `T+1`. -/
theorem gridBoundary_bounds (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : eta ≤ 1 /
      (1024 * (p.m : ℝ) * p.K * CanonicalRecordingRates.L_stab p))
    (sigma : Fin p.T) :
    sigma.val + 1 < gridBoundary p eta sigma ∧
      gridBoundary p eta sigma ≤ p.T + 1 := by
  let H := ReplayWeightStability.episodeHorizon eta
  have hH : 0 < H := episodeHorizon_pos_of_source_cap p eta heta hcap
  have hx : 0 < sigma.val + 1 := by omega
  have hmod : (sigma.val + 1) % H < H := Nat.mod_lt _ hH
  have hdiv : (sigma.val + 1) % H + H * ((sigma.val + 1) / H) = sigma.val + 1 :=
    Nat.mod_add_div _ _
  have hround : sigma.val + 1 < H * ((sigma.val + 1) / H + 1) := by
    rw [Nat.mul_succ]
    omega
  constructor
  · dsimp [gridBoundary, H]
    exact lt_min (by omega) hround
  · exact Nat.min_le_left _ _

/-- The literal first cutoff is strictly after the assignment start and no
later than the clipped grid endpoint. -/
theorem firstCutoff_bounds (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : eta ≤ 1 /
      (1024 * (p.m : ℝ) * p.K * CanonicalRecordingRates.L_stab p))
    (sigma : Fin p.T) (bits : Fin p.T → Bool) :
    sigma.val + 1 < firstCutoff p eta sigma bits ∧
      firstCutoff p eta sigma bits ≤ gridBoundary p eta sigma := by
  have hg := gridBoundary_bounds p eta heta hcap sigma
  constructor
  · have hmem : firstCutoff p eta sigma bits ∈
        firstCutoffCarrier p eta sigma bits := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hmem with hgrid | hevent
    · rw [hgrid]
      exact hg.1
    · obtain ⟨i, hi, hu⟩ := Finset.mem_image.mp hevent
      have hiCoord := (Finset.mem_filter.mp hi).1
      simp only [proposalCoordinates, Finset.mem_filter, Finset.mem_univ,
        true_and] at hiCoord
      have hstart := hiCoord.1
      rw [← hu]
      simp only [proposalEndpoint]
      omega
  · exact Finset.min'_le (firstCutoffCarrier p eta sigma bits)
      (gridBoundary p eta sigma) (Finset.mem_insert_self _ _)

/-- The literal known endpoint lies strictly after the assignment start and at
most at `t+1`. -/
theorem knownCutoff_bounds (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : eta ≤ 1 /
      (1024 * (p.m : ℝ) * p.K * CanonicalRecordingRates.L_stab p))
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    sigma.val + 1 < knownCutoff p eta sigma t bits ∧
      knownCutoff p eta sigma t bits ≤ t.val + 2 := by
  have hg := gridBoundary_bounds p eta heta hcap sigma
  constructor
  · have hmem : knownCutoff p eta sigma t bits ∈
        knownCutoffCarrier p eta sigma t bits := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hmem with ht | hrest
    · rw [ht]
      omega
    · rcases Finset.mem_insert.mp hrest with hgrid | hevent
      · rw [hgrid]
        exact hg.1
      · obtain ⟨i, hi, hu⟩ := Finset.mem_image.mp hevent
        have hi' := Finset.mem_filter.mp hi
        have hiPast := (Finset.mem_filter.mp hi).1
        have hiCoord := (Finset.mem_filter.mp hiPast).1
        simp only [proposalCoordinates, Finset.mem_filter, Finset.mem_univ,
          true_and] at hiCoord
        have hσi := hiCoord.1
        rw [← hu]
        simp only [proposalEndpoint]
        omega
  · exact Finset.min'_le (knownCutoffCarrier p eta sigma t bits)
      (t.val + 2) (Finset.mem_insert_self _ _)

/-- The inspected coordinates are exactly in the source's strict past and
before the grid endpoint. -/
theorem followerCutoffScan_inspected_source_bounds
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool)
    (i : Fin p.T)
    (hi : i ∈ (followerCutoffScan p eta sigma t hσt bits).inspected) :
    sigma.val + 1 ≤ i.val + 1 ∧ i.val + 1 < t.val + 1 ∧
      i.val + 1 < gridBoundary p eta sigma := by
  let coordinates := (pastProposalCoordinates p sigma t).sort (· ≤ ·)
  have hsubset := chronologicalScanLoop_inspected_subset bits
    (min (t.val + 2) (gridBoundary p eta sigma)) (gridBoundary p eta sigma)
    coordinates i hi
  have hcoord : i ∈ pastProposalCoordinates p sigma t := by
    have := hsubset
    simpa only [coordinates, Finset.mem_sort] using this
  have hgrid := chronologicalScanLoop_inspected_before_grid bits
    (min (t.val + 2) (gridBoundary p eta sigma)) (gridBoundary p eta sigma)
    coordinates i hi
  simp only [pastProposalCoordinates, Finset.mem_filter, proposalCoordinates,
    Finset.mem_filter, Finset.mem_univ, true_and] at hcoord
  refine ⟨by omega, by omega, hgrid⟩

/-- The actual read list is strictly chronological and therefore contains no
duplicate proposal coordinates. -/
theorem followerCutoffScan_inspected_pairwise
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    ((followerCutoffScan p eta sigma t hσt bits).inspected).Pairwise
      (fun i j => i.val < j.val) := by
  let coordinates := (pastProposalCoordinates p sigma t).sort (· ≤ ·)
  have hordered : coordinates.Pairwise fun i j => i.val < j.val := by
    dsimp [coordinates]
    simpa only [Fin.lt_def] using
      (Finset.sortedLT_sort (pastProposalCoordinates p sigma t)).pairwise
  exact chronologicalScanLoop_inspected_pairwise bits
    (min (t.val + 2) (gridBoundary p eta sigma)) (gridBoundary p eta sigma)
    coordinates hordered

/-- In particular, the explicit read list has no duplicate coordinates. -/
theorem followerCutoffScan_inspected_nodup
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    (followerCutoffScan p eta sigma t hσt bits).inspected.Nodup := by
  exact (followerCutoffScan_inspected_pairwise p eta sigma t hσt bits).nodup

/-- Every inspected coordinate precedes the returned endpoint. Therefore, when
`ell ≤ t`, every proposal coordinate in `[ell,t)` is unread. -/
theorem followerCutoffScan_inspected_before_endpoint
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool)
    (i : Fin p.T)
    (hi : i ∈ (followerCutoffScan p eta sigma t hσt bits).inspected) :
    i.val + 1 <
      (followerCutoffScan p eta sigma t hσt bits).endpoint := by
  let coordinates := (pastProposalCoordinates p sigma t).sort (· ≤ ·)
  have hordered : coordinates.Pairwise fun a b => a.val < b.val := by
    dsimp [coordinates]
    simpa only [Fin.lt_def] using
      (Finset.sortedLT_sort (pastProposalCoordinates p sigma t)).pairwise
  have hbefore : ∀ j ∈ coordinates, j.val + 1 < t.val + 2 := by
    intro j hj
    have hj' : j ∈ pastProposalCoordinates p sigma t := by
      simpa only [coordinates, Finset.mem_sort] using hj
    simp only [pastProposalCoordinates, Finset.mem_filter, proposalCoordinates,
      Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    omega
  exact chronologicalScanLoop_inspected_before_endpoint bits (t.val + 2)
    (gridBoundary p eta sigma) coordinates hordered hbefore i hi

/-- Every coordinate in the unread source suffix `[ell,t)` is absent from the
read list. Calendar rounds are interpreted one-based as `index.val + 1`. -/
theorem followerCutoffScan_unread_suffix
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool)
    (i : Fin p.T)
    (hEll : (followerCutoffScan p eta sigma t hσt bits).endpoint ≤ i.val + 1) :
    i ∉ (followerCutoffScan p eta sigma t hσt bits).inspected := by
  intro hiRead
  have hBefore := followerCutoffScan_inspected_before_endpoint
    p eta sigma t hσt bits i hiRead
  omega

/-- The proposal coordinate at the current decision round is not read. This
holds also at `t=T`, where the actual first-cutoff carrier separately excludes
the terminal `B_T` coordinate by its strict `s<T` condition. -/
theorem followerCutoffScan_does_not_read_current
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    t ∉ (followerCutoffScan p eta sigma t hσt bits).inspected := by
  intro ht
  have hsource := followerCutoffScan_inspected_source_bounds
    p eta sigma t hσt bits t ht
  omega

/-- The terminal table coordinate is excluded from the actual first-cutoff
proposal carrier, exactly because its source round is `T` rather than `<T`. -/
theorem terminalCoordinate_not_in_proposalCoordinates
    (p : ConstructorDimensions.Parameters) (sigma t : Fin p.T)
    (ht : t.val + 1 = p.T) :
    t ∉ proposalCoordinates p sigma := by
  intro htmem
  simp only [proposalCoordinates, Finset.mem_filter, Finset.mem_univ,
    true_and] at htmem
  omega

/-- Changing any uninspected proposal coordinates preserves both the scan
endpoint and its explicit read list. The hypothesis constrains only coordinates
that the first scan actually read. -/
theorem followerCutoffScan_noninterference
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val)
    (bits bits' : Fin p.T → Bool)
    (hagree : ∀ i ∈ (followerCutoffScan p eta sigma t hσt bits).inspected,
      bits i = bits' i) :
    followerCutoffScan p eta sigma t hσt bits =
      followerCutoffScan p eta sigma t hσt bits' := by
  exact chronologicalScanLoop_noninterference bits bits'
    (min (t.val + 2) (gridBoundary p eta sigma)) (gridBoundary p eta sigma)
    ((pastProposalCoordinates p sigma t).sort (· ≤ ·)) hagree

/-- The literal known endpoint agrees with `min(u,t+1)`, including proposals
at `s=t`, the terminal round, and starts on a grid boundary. -/
theorem followerCutoffScan_endpoint_bounds
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (hcap : eta ≤ 1 /
      (1024 * (p.m : ℝ) * p.K * CanonicalRecordingRates.L_stab p))
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val) (bits : Fin p.T → Bool) :
    sigma.val + 1 <
        (followerCutoffScan p eta sigma t hσt bits).endpoint ∧
      (followerCutoffScan p eta sigma t hσt bits).endpoint ≤ t.val + 2 ∧
      (followerCutoffScan p eta sigma t hσt bits).endpoint =
        min (firstCutoff p eta sigma bits) (t.val + 2) := by
  have hknown := knownCutoff_bounds p eta heta hcap sigma t hσt bits
  have hscan := followerCutoffScan_endpoint_eq_knownCutoff
    p eta sigma t hσt bits
  refine ⟨?_, ?_, ?_⟩
  · rw [hscan]
    exact hknown.1
  · rw [hscan]
    exact hknown.2
  · exact followerCutoffScan_endpoint_eq_min_firstCutoff p eta sigma t hσt bits

/-- The row-specialized scan reads only the selected complete row's `prop`
scalar at each inspected calendar coordinate. -/
noncomputable def completeRowCutoffScan (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val)
    (row : CompletePublicTable.CompleteRow p) : ScanResult p.T :=
  followerCutoffScan p eta sigma t hσt (completeRowProposalBit p eta row)

/-- Equality of the selected row's `prop` scalars on the inspected coordinates
preserves its row-specialized scan; other labels and all other rows are absent
from the input. -/
theorem completeRowCutoffScan_noninterference
    (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (sigma t : Fin p.T) (hσt : sigma.val ≤ t.val)
    (row row' : CompletePublicTable.CompleteRow p)
    (hprop : ∀ i ∈ (completeRowCutoffScan p eta sigma t hσt row).inspected,
      (CompletePublicTable.completeRowLearning p row i).1
          (ContinuousControlSlice.Label.prop) =
        (CompletePublicTable.completeRowLearning p row' i).1
          (ContinuousControlSlice.Label.prop)) :
    completeRowCutoffScan p eta sigma t hσt row =
      completeRowCutoffScan p eta sigma t hσt row' := by
  apply followerCutoffScan_noninterference
  intro i hi
  simp only [completeRowProposalBit, thresholdProposalBit, proposalHazard]
  rw [hprop i hi]

end Bandits.Support.FollowerCutoffScan

end
