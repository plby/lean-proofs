/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TriangleCollisionCounts
import ErdosProblems.Erdos207.RelationPairSupersets

/-! # The actual non-vertex-disjoint forbidden hypergraph -/

namespace Erdos207

open Finset

noncomputable section

def auxiliaryNonDisjointFamily
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (k : ℕ) : Finset (Finset I) :=
  uniformSupersets k (relationPairFamily (auxiliaryTriangleCollision e))

theorem mem_auxiliaryNonDisjointFamily_iff
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (k : ℕ) (E : Finset I) :
    E ∈ auxiliaryNonDisjointFamily e k ↔
      E.card = k ∧ ¬ (E : Set I).PairwiseDisjoint (fun i ↦ (e i).1) := by
  classical
  rw [auxiliaryNonDisjointFamily, mem_uniformSupersets_iff]
  constructor
  · rintro ⟨hcard, C, hC, hCE⟩
    obtain ⟨i, j, hij, hR, rfl⟩ := (mem_relationPairFamily_iff _ C).mp hC
    refine ⟨hcard, fun hp ↦ hR (hp ?_ ?_ hij)⟩
    · exact hCE (by simp)
    · exact hCE (by simp)
  · rintro ⟨hcard, hbad⟩
    refine ⟨hcard, ?_⟩
    by_contra hnone
    apply hbad
    intro i hi j hj hij
    by_contra hnot
    apply hnone
    refine ⟨{i, j}, (mem_relationPairFamily_iff _ _).mpr ⟨i, j, hij, hnot, rfl⟩, ?_⟩
    exact insert_subset hi (singleton_subset_iff.mpr hj)

theorem auxiliaryNonDisjointFamily_max_degree_le
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U)
    (k : ℕ) (hk : 2 ≤ k) :
    finiteHypergraphMaxDegree (auxiliaryNonDisjointFamily e k) ≤
      6 * U.card ^ 2 * (Fintype.card I) ^ (k - 2) := by
  have h := relationPairSupersets_max_degree_le (auxiliaryTriangleCollision e)
    (auxiliaryTriangleCollision_symmetric e) (3 * U.card ^ 2) k hk
    (card_auxiliary_collision_neighbors_le e U hsupport)
  have he : 2 * (3 * U.card ^ 2) = 6 * U.card ^ 2 := by ring
  simpa only [auxiliaryNonDisjointFamily, he] using h

theorem auxiliaryNonDisjointFamily_max_degree_le_vertex_power
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U)
    (k : ℕ) (hk : 2 ≤ k) :
    finiteHypergraphMaxDegree (auxiliaryNonDisjointFamily e k) ≤ 6 * U.card ^ (3 * k - 4) := by
  apply (auxiliaryNonDisjointFamily_max_degree_le e U hsupport k hk).trans
  calc
    _ ≤ 6 * U.card ^ 2 * (U.card ^ 3) ^ (k - 2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (card_auxiliary_triangles_le e U hsupport) _)
    _ = _ := by
      rw [← pow_mul, mul_assoc, ← pow_add]
      have he : 2 + 3 * (k - 2) = 3 * k - 4 := by omega
      rw [he]

end

end Erdos207
