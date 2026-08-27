/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousWeightedJointInclusion
import ErdosProblems.Erdos207.VortexLevelGreedy

/-!
# A time-scheduled multi-level vortex kernel

This is the flattened probabilistic form of a vortex sweep.  An arbitrary
schedule chooses the active level at every time.  Its joint-inclusion bound
retains the cumulative hazard of each individual triangle, so a later block
schedule can be compared directly with `vortexTripleWeight`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The threshold-stopped vortex kernel at the level selected by time `i`. -/
def scheduledStoppedVortexGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (i : ℕ) : GreedyStateOn V → FiniteLaw (GreedyStateOn V) :=
  stoppedVortexLevelGreedyKernel F W (schedule i) (D (schedule i))

/-- Law of the first `fuel` scheduled vortex transitions. -/
def scheduledStoppedVortexGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (fuel : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.evolveKernels
    (scheduledStoppedVortexGreedyKernel F W schedule D) fuel
    (FiniteLaw.pure S)

/-- Point hazard of one scheduled transition. -/
def scheduledVortexPointHazard
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (schedule : ℕ → Fin (ell + 1))
    (D : Fin (ell + 1) → ℕ) (i : ℕ) (T : TripleOn V) : ℝ≥0 :=
  if W.level T = schedule i then (D (schedule i) : ℝ≥0)⁻¹ else 0

/-- Number of visits to a fixed level among the first `fuel` scheduled
transitions. -/
def scheduledLevelVisits
    {ell : ℕ} (schedule : ℕ → Fin (ell + 1))
    (k : Fin (ell + 1)) (fuel : ℕ) : ℕ :=
  ((range fuel).filter fun i ↦ schedule i = k).card

@[simp]
lemma scheduledLevelVisits_zero
    {ell : ℕ} (schedule : ℕ → Fin (ell + 1)) (k : Fin (ell + 1)) :
    scheduledLevelVisits schedule k 0 = 0 := by
  simp [scheduledLevelVisits]

lemma scheduledLevelVisits_succ
    {ell : ℕ} (schedule : ℕ → Fin (ell + 1))
    (k : Fin (ell + 1)) (fuel : ℕ) :
    scheduledLevelVisits schedule k (fuel + 1) =
      scheduledLevelVisits schedule k fuel +
        if schedule fuel = k then 1 else 0 := by
  classical
  unfold scheduledLevelVisits
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hsched
  · rw [card_insert_of_notMem (by simp)]
  · simp

lemma scheduledLevelVisits_eq_sum_indicator
    {ell : ℕ} (schedule : ℕ → Fin (ell + 1))
    (k : Fin (ell + 1)) (fuel : ℕ) :
    scheduledLevelVisits schedule k fuel =
      ∑ i ∈ range fuel, if schedule i = k then 1 else 0 := by
  classical
  unfold scheduledLevelVisits
  rw [card_eq_sum_ones, sum_filter]

theorem scheduledStoppedVortexGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ) (i : ℕ) :
    IsMonotoneSingleInsertionKernel
      (scheduledStoppedVortexGreedyKernel F W schedule D i)
      (fun S : GreedyStateOn V ↦ S.chosen) :=
  stoppedVortexLevelGreedyKernel_monotone_singleInsertion
    F W (schedule i) (D (schedule i))

theorem scheduledStoppedVortexGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (hD : ∀ k, 0 < D k) (i : ℕ) (S : GreedyStateOn V)
    (T : TripleOn V) (hTnot : T ∉ S.chosen) :
    (scheduledStoppedVortexGreedyKernel F W schedule D i S).probability
        (fun S' ↦ T ∈ S'.chosen) ≤
      scheduledVortexPointHazard W schedule D i T := by
  exact stoppedVortexLevelGreedyKernel_probability_new_triangle_le
    F W (schedule i) (D (schedule i)) (hD (schedule i)) S T hTnot

/-- If the scheduled level is still above threshold, a supported transition
is a genuine insertion and increases the selected cardinality by one. -/
theorem scheduledStoppedVortexGreedyKernel_supported_chosen_card_succ
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {schedule : ℕ → Fin (ell + 1)} {D : Fin (ell + 1) → ℕ}
    {i : ℕ} {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant F A S)
    (hD : 0 < D (schedule i))
    (hactive : D (schedule i) ≤
      (vortexLevelAvailable W (schedule i) S).card) :
    (scheduledStoppedVortexGreedyKernel F W schedule D i S).SupportedOn
      (fun S' ↦ S'.chosen.card = S.chosen.card + 1) := by
  unfold scheduledStoppedVortexGreedyKernel
  unfold stoppedVortexLevelGreedyKernel
  simp only [hactive, if_true]
  have hnonempty :
      (vortexLevelAvailable W (schedule i) S).Nonempty := by
    rw [← card_pos]
    exact hD.trans_le hactive
  have hsteps := vortexLevelGreedyKernel_supported_step_of_nonempty
    F W (schedule i) S hnonempty
  intro S' hmass
  obtain ⟨T, hT, rfl⟩ := hsteps S' hmass
  have hTavailable : T ∈ S.available :=
    (mem_vortexLevelAvailable_iff.mp hT).1
  have hTnot : T ∉ S.chosen := (hS.1.2.2 T hTavailable).1
  simp [greedyStep, card_insert_of_notMem hTnot]

/-- Every scheduled transition preserves the absorber-greedy invariant. -/
theorem scheduledStoppedVortexGreedyProcessLaw_supported_absorberInvariant
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {schedule : ℕ → Fin (ell + 1)} {D : Fin (ell + 1) → ℕ}
    {S₀ : GreedyStateOn V} (hS₀ : AbsorberGreedyInvariant F A S₀) :
    ∀ fuel,
      (scheduledStoppedVortexGreedyProcessLaw
        F W schedule D fuel S₀).SupportedOn (AbsorberGreedyInvariant F A) := by
  intro fuel
  exact (FiniteLaw.supportedOn_pure _ hS₀).evolveKernels
    (scheduledStoppedVortexGreedyKernel F W schedule D)
    (fun i S hS ↦
      stoppedVortexLevelGreedyKernel_supported_absorberInvariant hS)
    fuel

/-- Global availability can only shrink during a scheduled process. -/
theorem scheduledStoppedVortexGreedyProcessLaw_supported_available_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (S₀ : GreedyStateOn V) :
    ∀ fuel,
      (scheduledStoppedVortexGreedyProcessLaw
        F W schedule D fuel S₀).SupportedOn
          (fun S ↦ S.available ⊆ S₀.available) := by
  intro fuel
  induction fuel with
  | zero => exact FiniteLaw.supportedOn_pure _ Subset.rfl
  | succ fuel ih =>
      change (FiniteLaw.bind
        (scheduledStoppedVortexGreedyProcessLaw
          F W schedule D fuel S₀)
        (scheduledStoppedVortexGreedyKernel F W schedule D fuel)).SupportedOn _
      exact ih.bind _ fun S hS S' hmass ↦
        (stoppedVortexLevelGreedyKernel_supported_available_subset
          F W (schedule fuel) (D (schedule fuel)) S S' hmass).trans hS

/-- The selected family can only grow during a scheduled process. -/
theorem scheduledStoppedVortexGreedyProcessLaw_supported_chosen_superset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (S₀ : GreedyStateOn V) :
    ∀ fuel,
      (scheduledStoppedVortexGreedyProcessLaw
        F W schedule D fuel S₀).SupportedOn
          (fun S ↦ S₀.chosen ⊆ S.chosen) := by
  intro fuel
  induction fuel with
  | zero => exact FiniteLaw.supportedOn_pure _ Subset.rfl
  | succ fuel ih =>
      change (FiniteLaw.bind
        (scheduledStoppedVortexGreedyProcessLaw
          F W schedule D fuel S₀)
        (scheduledStoppedVortexGreedyKernel F W schedule D fuel)).SupportedOn _
      refine ih.bind _ ?_
      intro S hS S' hmass
      exact hS.trans
        ((scheduledStoppedVortexGreedyKernel_monotone_singleInsertion
          F W schedule D fuel S S' hmass).1)

/-- For each fixed level, a scheduled process either reaches its threshold
or performs at least one insertion for every visit to that level. -/
theorem scheduledStoppedVortexGreedyProcessLaw_supported_levelProgress
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {schedule : ℕ → Fin (ell + 1)} {D : Fin (ell + 1) → ℕ}
    (hD : ∀ k, 0 < D k) {S₀ : GreedyStateOn V}
    (hS₀ : AbsorberGreedyInvariant F A S₀) (k : Fin (ell + 1)) :
    ∀ fuel,
      (scheduledStoppedVortexGreedyProcessLaw
        F W schedule D fuel S₀).SupportedOn
          (fun S ↦ AbsorberGreedyInvariant F A S ∧
            S.available ⊆ S₀.available ∧
            ((vortexLevelAvailable W k S).card < D k ∨
              S₀.chosen.card + scheduledLevelVisits schedule k fuel ≤
                S.chosen.card)) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _
        ⟨hS₀, Subset.rfl, Or.inr (by simp)⟩
  | succ fuel ih =>
      change (FiniteLaw.bind
        (scheduledStoppedVortexGreedyProcessLaw
          F W schedule D fuel S₀)
        (scheduledStoppedVortexGreedyKernel F W schedule D fuel)).SupportedOn _
      refine ih.bind _ ?_
      intro S hS S' hmass
      have hInv' :=
        stoppedVortexLevelGreedyKernel_supported_absorberInvariant
          hS.1 S' hmass
      have hAvailStep :=
        stoppedVortexLevelGreedyKernel_supported_available_subset
          F W (schedule fuel) (D (schedule fuel)) S S' hmass
      have hAvail' : S'.available ⊆ S₀.available :=
        hAvailStep.trans hS.2.1
      refine ⟨hInv', hAvail', ?_⟩
      by_cases hsmall' : (vortexLevelAvailable W k S').card < D k
      · exact Or.inl hsmall'
      · apply Or.inr
        have hlevelSub : vortexLevelAvailable W k S' ⊆
            vortexLevelAvailable W k S := by
          intro T hT
          rw [mem_vortexLevelAvailable_iff] at hT ⊢
          exact ⟨hAvailStep hT.1, hT.2⟩
        have hactiveK : D k ≤ (vortexLevelAvailable W k S).card :=
          (Nat.le_of_not_gt hsmall').trans (card_le_card hlevelSub)
        have hprevious :
            S₀.chosen.card + scheduledLevelVisits schedule k fuel ≤
              S.chosen.card := by
          rcases hS.2.2 with hsmall | hlarge
          · omega
          · exact hlarge
        by_cases hsched : schedule fuel = k
        · have hactive : D (schedule fuel) ≤
              (vortexLevelAvailable W (schedule fuel) S).card := by
            simpa only [hsched] using hactiveK
          have hcard :=
            scheduledStoppedVortexGreedyKernel_supported_chosen_card_succ
              hS.1 (hD (schedule fuel)) hactive S' hmass
          rw [scheduledLevelVisits_succ, if_pos hsched, hcard]
          omega
        · have hchosenSub : S.chosen ⊆ S'.chosen :=
            (scheduledStoppedVortexGreedyKernel_monotone_singleInsertion
              F W schedule D fuel S S' hmass).1
          have hcardMono := card_le_card hchosenSub
          rw [scheduledLevelVisits_succ, if_neg hsched]
          omega

/-- Exact point-weighted joint-inclusion estimate for a scheduled sweep. -/
theorem scheduledStoppedVortexGreedy_probability_subset_chosen_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (hD : ∀ k, 0 < D k) (fuel : ℕ) (S : GreedyStateOn V)
    (U : TripleSystemOn V) (hdisjoint : Disjoint U S.chosen) :
    (scheduledStoppedVortexGreedyProcessLaw
        F W schedule D fuel S).probability (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        setWeight
          (cumulativePointHazard
            (scheduledVortexPointHazard W schedule D) fuel) U := by
  exact evolveKernels_probability_subset_le_pointWeights
    (scheduledStoppedVortexGreedyKernel F W schedule D)
    (fun S : GreedyStateOn V ↦ S.chosen)
    (scheduledVortexPointHazard W schedule D)
    (scheduledStoppedVortexGreedyKernel_monotone_singleInsertion
      F W schedule D)
    (scheduledStoppedVortexGreedyKernel_probability_new_triangle_le
      F W schedule D hD)
    S U hdisjoint fuel

/-- If the cumulative scheduled hazard of every triangle is bounded by the
vortex weight, then the whole scheduled sweep has the desired factorial
joint-inclusion estimate. -/
theorem scheduledStoppedVortexGreedy_probability_subset_chosen_le_vortexWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (schedule : ℕ → Fin (ell + 1)) (D : Fin (ell + 1) → ℕ)
    (hD : ∀ k, 0 < D k) (fuel : ℕ) (c : ℝ≥0)
    (hratio : ∀ T : TripleOn V,
      cumulativePointHazard
          (scheduledVortexPointHazard W schedule D) fuel T ≤
        vortexTripleWeight W c T)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) :
    (scheduledStoppedVortexGreedyProcessLaw
        F W schedule D fuel S).probability (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) * setWeight (vortexTripleWeight W c) U := by
  apply (scheduledStoppedVortexGreedy_probability_subset_chosen_le
    F W schedule D hD fuel S U hdisjoint).trans
  gcongr
  unfold setWeight
  apply prod_le_prod
  · intro T hTU
    exact bot_le
  · intro T hTU
    exact hratio T

end

end Erdos207
