/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyJointInclusion
import ErdosProblems.Erdos207.VertexStarWeight
import ErdosProblems.Erdos207.CompatibleCandidateDegree

/-!
# Vertex-star moments in the stopped greedy process

The number of chosen triangles through one vertex is a singleton-family
configuration count.  Its extension budget is linear in the ambient order
at weight `(n+1)⁻¹`, so the general moment lemma gives simultaneous vertex
degree control at the same scale.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The exact singleton-star budget is bounded uniformly by `|V|+2` at the
standard triangle weight. -/
theorem singletonVertexStar_extensionBudget_le_card_add_two
    (V : Type*) [Fintype V] [DecidableEq V] (v : V) :
    ((universeTriplesThrough v).card : ℝ≥0) *
        (Fintype.card V + 1 : ℝ≥0)⁻¹ + 1 ≤
      (Fintype.card V + 2 : ℕ) := by
  have hstar : ((universeTriplesThrough v).card : ℝ≥0) ≤
      (Fintype.card V : ℝ≥0) ^ 2 := by
    exact_mod_cast card_universeTriplesThrough_le_sq V v
  calc
    ((universeTriplesThrough v).card : ℝ≥0) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹ + 1 ≤
        (Fintype.card V : ℝ≥0) ^ 2 *
          (Fintype.card V + 1 : ℝ≥0)⁻¹ + 1 := by
      gcongr
    _ ≤ (Fintype.card V + 1 : ℕ) + 1 := by
      gcongr
      simpa using card_sq_mul_inv_add_one_le (Fintype.card V)
    _ = (Fintype.card V + 2 : ℕ) := by
      push_cast
      ring

/-- Concrete moment bound for the selected vertex star in a stopped greedy
law whose cumulative point scale is at most `(n+1)⁻¹`. -/
theorem stoppedGreedy_triplesThrough_momentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {D fuel s : ℕ} {F : ForbiddenFamilyOn V}
    {S₀ : GreedyStateOn V} (v : V)
    (hD : 0 < D) (hchosen : S₀.chosen = ∅)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (stoppedGreedyProcessLaw F D fuel S₀).expectation
      (fun S ↦ ((triplesThrough S.chosen v).card : ℝ≥0) ^ s) ≤
      (s.factorial : ℝ≥0) *
        (((2 : ℝ≥0) ^ s * (Fintype.card V + 2 : ℕ)) ^ s) := by
  let L := stoppedGreedyProcessLaw F D fuel S₀
  have hmoment := configurationMomentBound L
    (fun T : universeTriplesThrough v ↦ ({T.1} : TripleSystemOn V))
    (fun S : GreedyStateOn V ↦ S.chosen)
    (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (s.factorial : ℝ≥0) (Fintype.card V + 2 : ℕ)
    (d := 1) (s := s)
    (by intro T; simp)
    (by
      intro H
      exact (singletonVertexStar_hasExtensionBound v
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) H).trans
          (singletonVertexStar_extensionBudget_le_card_add_two V v))
    (by
      intro T hTcard
      apply stoppedGreedyProcess_probability_subset_chosen_le_weight
        F D fuel s hD ((Fintype.card V + 1 : ℝ≥0)⁻¹)
        hratio S₀ T
      · simp [hchosen]
      · simpa using hTcard)
  simpa [L, selectedCount_singletonVertexStar] using hmoment

/-- Markov consequence for one vertex-star count. -/
theorem stoppedGreedy_probability_triplesThrough_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {D fuel s : ℕ} {F : ForbiddenFamilyOn V}
    {S₀ : GreedyStateOn V} (v : V) (a : ℝ≥0)
    (hD : 0 < D) (ha : 0 < a) (hchosen : S₀.chosen = ∅)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability
        (fun S ↦ a ≤ (triplesThrough S.chosen v).card) ≤
      ((s.factorial : ℝ≥0) *
        (((2 : ℝ≥0) ^ s * (Fintype.card V + 2 : ℕ)) ^ s)) /
          a ^ s := by
  let L := stoppedGreedyProcessLaw F D fuel S₀
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
  exact hmarkov.trans ((div_le_div_iff_of_pos_right (pow_pos ha s)).2
    (stoppedGreedy_triplesThrough_momentBound v hD hchosen hratio))

/-- A strict union-bound inequality extracts one stopped trajectory with all
vertex-star counts below the same threshold. -/
theorem exists_stoppedGreedy_all_triplesThrough_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {D fuel s : ℕ} {F : ForbiddenFamilyOn V}
    {S₀ : GreedyStateOn V} (a : ℝ≥0)
    (hD : 0 < D) (ha : 0 < a) (hchosen : S₀.chosen = ∅)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall : (Fintype.card V : ℝ≥0) *
      (((s.factorial : ℝ≥0) *
        (((2 : ℝ≥0) ^ s * (Fintype.card V + 2 : ℕ)) ^ s)) /
          a ^ s) < 1) :
    ∃ S : GreedyStateOn V, ∀ v : V,
      ((triplesThrough S.chosen v).card : ℝ≥0) < a := by
  let L := stoppedGreedyProcessLaw F D fuel S₀
  let bad : V → GreedyStateOn V → Prop :=
    fun v S ↦ a ≤ (triplesThrough S.chosen v).card
  have hsum : ∑ v : V, L.probability (bad v) < 1 := by
    calc
      ∑ v : V, L.probability (bad v) ≤
          ∑ _v : V,
            ((s.factorial : ℝ≥0) *
              (((2 : ℝ≥0) ^ s * (Fintype.card V + 2 : ℕ)) ^ s)) /
                a ^ s := by
        apply Finset.sum_le_sum
        intro v _hv
        exact stoppedGreedy_probability_triplesThrough_ge_le
          v a hD ha hchosen hratio
      _ = (Fintype.card V : ℝ≥0) *
          (((s.factorial : ℝ≥0) *
            (((2 : ℝ≥0) ^ s * (Fintype.card V + 2 : ℕ)) ^ s)) /
              a ^ s) := by simp
      _ < 1 := hsmall
  obtain ⟨S, hS⟩ := L.exists_avoiding_of_sum_probability_lt_one
    (univ : Finset V) bad (by simpa using hsum)
  exact ⟨S, fun v ↦ lt_of_not_ge (hS v (mem_univ v))⟩

end

end Erdos207
