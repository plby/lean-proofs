/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexCyclicSweep
import ErdosProblems.Erdos207.VertexStarWeight

/-!
# Vertex-star moments for the cyclic vortex sweep

The inhomogeneous joint-inclusion estimate for the common cyclic law also
controls every vertex star.  Unlike the constant-weight estimate, its
extension budget records the exact vortex weight of the ambient star.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Exact point-weight extension budget of the singleton star at `v`. -/
def vortexVertexStarExtensionBudget
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (c : ℝ≥0) (v : V) : ℝ≥0 :=
  (∑ T : universeTriplesThrough v, vortexTripleWeight W c T.1) + 1

/-- Moment bound for one selected vertex star under the cyclic vortex law. -/
theorem cyclicVortexGreedy_vertexStarMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q s : ℕ} (W : Vortex V ell) (B A : TripleSystemOn V)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (c : ℝ≥0)
    (hratio : ∀ k : Fin (ell + 1),
      (vortexPackingSaturationFuel V : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤
        c / (W.U k).card)
    (v : V) :
    (scheduledStoppedVortexGreedyProcessLaw
      (absorberErdosForbiddenConfigurationsOn q B) W
      (vortexCyclicSchedule ell) D
      (vortexPackingSaturationFuel V * (ell + 1))
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
        (fun S ↦ ((triplesThrough S.chosen v).card : ℝ≥0) ^ s) ≤
      (s.factorial : ℝ≥0) *
        (((2 : ℝ≥0) ^ s * vortexVertexStarExtensionBudget W c v) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let cycles := vortexPackingSaturationFuel V
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D (cycles * (ell + 1)) S₀
  have hmoment := configurationMomentBound L
    (fun T : universeTriplesThrough v ↦ ({T.1} : TripleSystemOn V))
    (fun S : GreedyStateOn V ↦ S.chosen)
    (vortexTripleWeight W c)
    (s.factorial : ℝ≥0) (vortexVertexStarExtensionBudget W c v)
    (d := 1) (s := s)
    (by intro T; simp)
    (singletonVertexStar_hasExtensionBound_pointWeight v
      (vortexTripleWeight W c))
    (fun T hTcard ↦ by
      have hjoint :=
        cyclicVortexGreedy_probability_subset_chosen_le_vortexWeight
          F W D hD cycles c hratio S₀ T (by
            simp [S₀, absorberGreedyInitialState])
      apply hjoint.trans
      gcongr
      simpa using hTcard)
  simpa only [L, F, S₀, cycles, Nat.mul_one,
    selectedCount_singletonVertexStar,
    vortexVertexStarExtensionBudget] using hmoment

/-- Markov bound for one vertex star under the same cyclic law. -/
theorem cyclicVortexGreedy_probability_vertexStar_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q s : ℕ} (W : Vortex V ell) (B A : TripleSystemOn V)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (c a : ℝ≥0) (ha : 0 < a)
    (hratio : ∀ k : Fin (ell + 1),
      (vortexPackingSaturationFuel V : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤
        c / (W.U k).card)
    (v : V) :
    (scheduledStoppedVortexGreedyProcessLaw
      (absorberErdosForbiddenConfigurationsOn q B) W
      (vortexCyclicSchedule ell) D
      (vortexPackingSaturationFuel V * (ell + 1))
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
        (fun S ↦ a ≤ (triplesThrough S.chosen v).card) ≤
      ((s.factorial : ℝ≥0) *
        (((2 : ℝ≥0) ^ s * vortexVertexStarExtensionBudget W c v) ^ s)) /
          a ^ s := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D
    (vortexPackingSaturationFuel V * (ell + 1)) S₀
  have hmono : L.probability
      (fun S ↦ a ≤ (triplesThrough S.chosen v).card) ≤
      L.probability (fun S ↦
        a ^ s ≤ ((triplesThrough S.chosen v).card : ℝ≥0) ^ s) := by
    apply L.probability_mono
    intro S hS
    exact pow_le_pow_left' hS s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div
    (fun S ↦ ((triplesThrough S.chosen v).card : ℝ≥0) ^ s)
    (pow_pos ha s)
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right (pow_pos ha s)).2
  exact cyclicVortexGreedy_vertexStarMomentBound
    W B A D hD c hratio v

/-- Under one explicit union-bound inequality, an outcome of the common
cyclic law has the structural conclusion and every vertex-star cutoff. -/
theorem exists_cyclicVortexGreedy_globalBound_all_vertexStars_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q s : ℕ} (W : Vortex V ell) (B A : TripleSystemOn V)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (c a : ℝ≥0) (ha : 0 < a)
    (hratio : ∀ k : Fin (ell + 1),
      (vortexPackingSaturationFuel V : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤
        c / (W.U k).card)
    (hsmall : ∑ v : V,
      (((s.factorial : ℝ≥0) *
        (((2 : ℝ≥0) ^ s * vortexVertexStarExtensionBudget W c v) ^ s)) /
          a ^ s) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
        (absorberErdosForbiddenConfigurationsOn q B) A S ∧
      S.available.card ≤ ∑ k, D k ∧
      S.available ⊆
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A).available ∧
      ∀ v : V, ((triplesThrough S.chosen v).card : ℝ≥0) < a := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D
    (vortexPackingSaturationFuel V * (ell + 1)) S₀
  let Good : GreedyStateOn V → Prop := fun S ↦
    AbsorberGreedyInvariant F A S ∧
      S.available.card ≤ ∑ k, D k ∧ S.available ⊆ S₀.available
  have hS₀ : AbsorberGreedyInvariant F A S₀ := by
    exact absorberGreedyInitialState_invariant F A fun C hC ↦
      absorberErdosForbidden_nonempty hC
  have hsupport : L.SupportedOn Good := by
    exact cyclicVortexGreedy_supported_globalBound hD hS₀
  let bad : Option V → GreedyStateOn V → Prop
    | none, S => ¬ Good S
    | some v, S => a ≤ (triplesThrough S.chosen v).card
  have hstruct : L.probability (bad none) = 0 := by
    change L.probability (fun S ↦ ¬ Good S) = 0
    rw [L.probability_not, L.probability_eq_one_of_supported Good hsupport]
    simp
  have hprob : ∀ v : V,
      L.probability (bad (some v)) ≤
        ((s.factorial : ℝ≥0) *
          (((2 : ℝ≥0) ^ s *
            vortexVertexStarExtensionBudget W c v) ^ s)) / a ^ s := by
    intro v
    exact cyclicVortexGreedy_probability_vertexStar_ge_le
      W B A D hD c a ha hratio v
  have hsum : ∑ i : Option V, L.probability (bad i) < 1 := by
    rw [Fintype.sum_option, hstruct, zero_add]
    exact lt_of_le_of_lt (sum_le_sum fun v _hv ↦ hprob v) hsmall
  obtain ⟨S, hS⟩ := L.exists_avoiding_of_sum_probability_lt_one
    (univ : Finset (Option V)) bad (by simpa using hsum)
  have hGood : Good S := not_not.mp (hS none (mem_univ none))
  refine ⟨S, hGood.1, hGood.2.1, hGood.2.2, ?_⟩
  intro v
  exact lt_of_not_ge (hS (some v) (mem_univ (some v)))

end

end Erdos207
